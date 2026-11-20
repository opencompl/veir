module

public import Veir.PatternRewriter.Puddle.CreationSemantics
public import Veir.Interpreter.Lemmas
public import Veir.PatternRewriter.Puddle.ExecutionLemmas
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.IR.Basic

namespace Veir.Puddle

public section

/-- Raw result installation, matching the default indexing in symbolic creation semantics.
Agreement with checked IR interpretation additionally requires conforming, correctly sized results. -/
@[expose]
def ValueResolver.setResultsDefault (resolve : ValueResolver) (op : OperationPtr)
    (values : Array RuntimeValue) : ValueResolver := fun pointer =>
  match pointer with
  | .opResult result => if result.op = op then some values[result.index]! else resolve pointer
  | .blockArgument _ => resolve pointer

@[simp]
theorem ValueResolver.setResultsDefault_getResult (resolve : ValueResolver) (op : OperationPtr)
    (values : Array RuntimeValue) (i : Nat) :
    resolve.setResultsDefault op values (.opResult (op.getResult i)) = some values[i]! := by
  simp [setResultsDefault, OperationPtr.getResult]

/-- Checked result installation agrees with raw pointer interpretation on every valid pointer. -/
theorem ValueResolver.setResultsDefault_eq_checked {ctx : WfIRContext OpCode}
    {state state' : VariableState ctx} {op : OperationPtr} {values : Array RuntimeValue}
    {hop : op.InBounds ctx.raw} (hset : state.setResultValues? op values hop = some state')
    (pointer : ValuePtr) (hptr : pointer.InBounds ctx.raw) :
    ValueResolver.setResultsDefault state.getVar? op values pointer = state'.getVar? pointer := by
  have hget := VariableState.getVar?_setResultValues? hset (value := pointer)
  cases pointer with
  | blockArgument => exact hget.symm
  | opResult result =>
    by_cases heq : result.op = op
    · have hindex : result.index < op.getNumResults! ctx.raw := by grind
      simpa [setResultsDefault, heq, hindex] using hget.symm
    · simpa [setResultsDefault, heq] using hget.symm

/-- Conforming raw results can always be installed by the checked interpreter. -/
theorem ValueResolver.exists_checked_result_state {ctx : WfIRContext OpCode}
    (state : VariableState ctx) {op : OperationPtr} (hop : op.InBounds ctx.raw)
    {values : Array RuntimeValue}
    (hconf : RuntimeValue.ArrayConforms values (op.getResultTypes! ctx.raw)) :
    ∃ state', state.setResultValues? op values hop = some state' ∧
      ∀ pointer, pointer.InBounds ctx.raw →
        ValueResolver.setResultsDefault state.getVar? op values pointer = state'.getVar? pointer := by
  obtain ⟨state', hset⟩ := (VariableState.setResultValues?_isSome_iff_conforms state hop).mp hconf
  exact ⟨state', hset, fun p hp => setResultsDefault_eq_checked hset p hp⟩

/-- An assignment's SSA pointers are valid in a concrete context. -/
def Assignment.ValuesInBounds (a : Assignment OpCode) (ctx : IRContext OpCode) : Prop :=
  ∀ (id : Nat) (pointer : ValuePtr), a.bindings[id]?.join = some (.value pointer) → pointer.InBounds ctx

/-- Raw fresh-result installation leaves the old assignment's semantic meaning unchanged. -/
theorem Assignment.denote_setResultsDefault_of_fresh {a : Assignment OpCode}
    (resolve : ValueResolver) (op : OperationPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (hbound : a.ValuesInBounds ctx.raw) (hfresh : ¬op.InBounds ctx.raw)
    (typeOf : ValuePtr → TypeAttr) :
    a.denote (resolve.setResultsDefault op values) typeOf = a.denote resolve typeOf := by
  apply Assignment.denote_congr_resolve
  intro id pointer hb
  have hp := hbound id pointer hb
  cases pointer with
  | blockArgument => rfl
  | opResult result =>
    have hne : result.op ≠ op := by grind
    simp [ValueResolver.setResultsDefault, hne]

/-- Concrete fresh result bindings agree with typed symbolic binding for every raw outcome. -/
theorem Assignment.denote_bindFreshOpResultsDefault {a middle b : Assignment OpCode}
    {opHandle : Handle OpCode .op} {handles : Array (Handle OpCode .value)}
    {op : OperationPtr} {oldCtx newCtx : WfIRContext OpCode}
    (resolve : ValueResolver) (values : Array RuntimeValue)
    (hop : a.bindOp opHandle op = some middle)
    (hbind : middle.bindValues handles.toList (op.getResults! newCtx.raw).toList = some b)
    (hbound : a.ValuesInBounds oldCtx.raw) (hfresh : ¬op.InBounds oldCtx.raw)
    (typeOf : ValuePtr → TypeAttr) :
    SemanticAssignment.bindValues values (a.denote resolve typeOf) handles.toList
      ((op.getResults! newCtx.raw).toList.map typeOf) =
      some (b.denote (resolve.setResultsDefault op values) typeOf) := by
  have hresolve : ∀ i, i < handles.toList.length →
      resolve.setResultsDefault op values (op.getResults! newCtx.raw).toList[i]! = some values[0 + i]! := by
    intro i hi
    have hlen := Assignment.bindValues_length hbind
    have hopi : i < op.getNumResults! newCtx.raw := by
      simp only [Array.length_toList, OperationPtr.getResults!.size_eq_getNumResults!] at hlen hi
      omega
    simp only [Array.getElem!_toList, OperationPtr.getResults!.getElem!_eq_getResult hopi,
      ValueResolver.setResultsDefault_getResult, Nat.zero_add]
  simpa only [Assignment.denote_bindOp _ hop typeOf,
      Assignment.denote_setResultsDefault_of_fresh resolve op values hbound hfresh typeOf] using
    Assignment.denote_bindValues (resolve.setResultsDefault op values) values 0 hbind hresolve typeOf

/-- Fresh result bindings carry the result types from the extended context. -/
theorem Assignment.denote_bindFreshOpResultsDefault_typed {a middle b : Assignment OpCode}
    {opHandle : Handle OpCode .op} {handles : Array (Handle OpCode .value)}
    {op : OperationPtr} {oldCtx newCtx : WfIRContext OpCode}
    (resolve : ValueResolver) (values : Array RuntimeValue)
    (hop : a.bindOp opHandle op = some middle)
    (hbind : middle.bindValues handles.toList (op.getResults! newCtx.raw).toList = some b)
    (hbound : a.ValuesInBounds oldCtx.raw) (hfresh : ¬op.InBounds oldCtx.raw)
    (htype : ∀ (pointer : ValuePtr), pointer.InBounds oldCtx.raw →
      pointer.getType! newCtx.raw = pointer.getType! oldCtx.raw) :
    SemanticAssignment.bindValues values (a.denote resolve (fun p => p.getType! oldCtx.raw))
      handles.toList (op.getResultTypes! newCtx.raw).toList =
      some (b.denote (resolve.setResultsDefault op values) (fun p => p.getType! newCtx.raw)) := by
  have htypes : (op.getResults! newCtx.raw).toList.map (fun p => p.getType! newCtx.raw) =
      (op.getResultTypes! newCtx.raw).toList := by
    simp [OperationPtr.getResultTypes!_def]
  have hdenote : a.denote resolve (fun p => p.getType! newCtx.raw) =
      a.denote resolve (fun p => p.getType! oldCtx.raw) := by
    apply Assignment.denote_congr_typeOf
    intro id pointer hb
    exact htype pointer (hbound id pointer hb)
  simpa only [htypes, hdenote] using
    Assignment.denote_bindFreshOpResultsDefault resolve values hop hbind hbound hfresh
      (fun p => p.getType! newCtx.raw)

/-- Context extension transports the bounds invariant. -/
theorem Assignment.ValuesInBounds.mono {a : Assignment OpCode} {ctx ctx' : IRContext OpCode}
    (h : a.ValuesInBounds ctx) (hctx : ∀ p : ValuePtr, p.InBounds ctx → p.InBounds ctx') :
    a.ValuesInBounds ctx' := by
  intro id pointer hb
  exact hctx pointer (h id pointer hb)

/-- Successful slot binding preserves valid pointers when the new binding is valid. -/
theorem Assignment.ValuesInBounds.bind {a b : Assignment OpCode} {ctx : IRContext OpCode}
    {kind : HandleType OpCode} {handle : Handle OpCode kind} {binding : Binding OpCode}
    (ha : a.ValuesInBounds ctx) (h : a.bind handle binding = some b)
    (hnew : ∀ pointer, binding = .value pointer → pointer.InBounds ctx) : b.ValuesInBounds ctx := by
  intro id pointer hb
  have hb' : b.getBinding (Handle.mk (handleType := .type) id) = some (.value pointer) := hb
  by_cases heq : id = handle.id
  · subst id
    have hinstalled := Assignment.getBinding_of_bind h
    have heq : binding = .value pointer := Option.some.inj (hinstalled.symm.trans hb')
    exact hnew pointer heq
  · rw [Assignment.getBinding_of_bind_of_ne _ h heq] at hb'
    exact ha id pointer hb'

/-- A list of valid pointers may be bound without invalidating other assignment pointers. -/
theorem Assignment.ValuesInBounds.bindValues {a b : Assignment OpCode} {ctx : IRContext OpCode}
    {handles : List (Handle OpCode .value)} {pointers : List ValuePtr}
    (ha : a.ValuesInBounds ctx) (h : a.bindValues handles pointers = some b)
    (hp : ∀ pointer ∈ pointers, pointer.InBounds ctx) : b.ValuesInBounds ctx := by
  induction handles generalizing a pointers with
  | nil => cases pointers <;> simp_all [Assignment.bindValues]
  | cons handle handles ih =>
    cases pointers with
    | nil => simp [Assignment.bindValues] at h
    | cons pointer pointers =>
      simp only [Assignment.bindValues, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hb, hr⟩ := h
      apply ih (ha.bind hb (by intro p heq; cases heq; exact hp pointer (by simp))) hr
      intro p hm
      exact hp p (by simp [hm])

/-- Metadata binding never introduces a new SSA pointer. -/
theorem MetadataTuple.Shape.valuesInBounds_bind
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    {a b : Assignment OpCode} {ctx : IRContext OpCode}
    (ha : a.ValuesInBounds ctx) (h : shape.bind a handles values = some b) : b.ValuesInBounds ctx := by
  induction shape generalizing a b with
  | unit => cases h; exact ha
  | atom atom =>
    cases atom <;> exact ha.bind h (by intro p heq; cases heq)
  | cons head tail ih =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hh, ht⟩ := h
    apply ih _ _ (a := middle) ?_ ht
    cases head <;> exact ha.bind hh (by intro p heq; cases heq)

/-- Every successful creation step preserves bounds-respecting assignment pointers. -/
theorem CreateDecl.valuesInBounds_of_run (decl : CreateDecl OpCode)
    {ctx newCtx : WfIRContext OpCode} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (ha : a.ValuesInBounds ctx.raw) (h : decl.run a ctx = some (newCtx, newOps, b)) :
    b.ValuesInBounds newCtx.raw := by
  cases decl with
  | operation code operandHandles typeHandles propertyHandle opHandle resultHandles =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨operands, hop, types, hty, properties, hprop, u, hguard, h⟩ := h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨createdCtx, op⟩, hcreate, bound, hbindop, final, hbindresults, heq⟩ := h
      cases heq
      have ha' : a.ValuesInBounds createdCtx.raw := ha.mono (by intro p hp; grind)
      have hb := ha'.bind hbindop (by intro p heq; cases heq)
      apply hb.bindValues hbindresults
      intro p hp
      have hopin := WfRewriter.createOp_new_inBounds op hcreate
      grind
    · contradiction
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨bound, hb, heq⟩ := h
    cases heq
    exact ha.bind hb (by intro p heq; cases heq)
  | property code value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨bound, hb, heq⟩ := h
    cases heq
    exact ha.bind hb (by intro p heq; cases heq)
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨values, _, outValues, _, bound, hb, heq⟩ := h
    cases heq
    exact MetadataTuple.Shape.valuesInBounds_bind _ _ _ ha hb

/-- Appending allocations preserves all semantic fields of operations already in bounds. -/
theorem WfIRContext.WithCreatedOps.operation_fields {ctx ctx' : WfIRContext OpCode}
    (h : Veir.WfIRContext.WithCreatedOps ctx ctx') (op : OperationPtr) (hop : op.InBounds ctx.raw) :
    op.getOpType! ctx'.raw = op.getOpType! ctx.raw ∧
    op.getResultTypes! ctx'.raw = op.getResultTypes! ctx.raw ∧
    op.getOperands! ctx'.raw = op.getOperands! ctx.raw ∧
    (∀ code : OpCode, op.getProperties! ctx'.raw code = op.getProperties! ctx.raw code) := by
  induction h with
  | Nil => exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | @CreatedOp newOp ctx₁ ctx₂ ctx₃ hprev hcreate ih =>
    have ih := ih hop
    obtain ⟨code, types, operands, successors, regions, properties, h₁, h₂, h₃, h₄, hcreate⟩ := hcreate
    have hbound := hprev.inBounds_mono (.operation op) hop
    have hfresh := WfRewriter.createOp_new_not_inBounds newOp hcreate
    have hne : op ≠ newOp := by grind
    have hc := OperationPtr.getOpType!_WfRewriter_createOp hcreate (operation := op)
    have ht := OperationPtr.getResultTypes!_WfRewriter_createOp hcreate (operation := op)
    have ho := OperationPtr.getOperands!_WfRewriter_createOp hcreate (operation := op)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hne, ih.1] using hc
    · simpa [hne, ih.2.1] using ht
    · simpa [hne, ih.2.2.1] using ho
    · intro c
      have hp := OperationPtr.getProperties!_WfRewriter_createOp hcreate (operation := op) (dialectOpType := c)
      simpa [hne, ih.2.2.2 c] using hp

/-- A declaration returns either no operations or the single fresh operation it created. -/
theorem CreateDecl.run_ops_shape (decl : CreateDecl OpCode)
    {ctx newCtx : WfIRContext OpCode} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (h : decl.run a ctx = some (newCtx, newOps, b)) :
    newOps = #[] ∨ ∃ op, newOps = #[op] ∧ op.InBounds newCtx.raw := by
  cases decl <;> simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def] at h
  all_goals
    repeat first
      | obtain ⟨_, _, h⟩ := h
      | split at h
      | simp only [Option.bind_eq_some_iff] at h
  all_goals first
    | exact Or.inl rfl
    | contradiction
    | right; exact ⟨_, rfl, by grind⟩

namespace CTree

/-- Raw interpretation of one allocated operation using concrete pointer lookups. -/
@[expose]
def interpretCreatedOp (ctx : IRContext OpCode) (op : OperationPtr) (resolve : ValueResolver)
    (memory : MemoryState) (next : ValueResolver → MemoryState → Tree α) : Tree α :=
  match (op.getOperands! ctx).toList.mapM resolve with
  | none => fail
  | some operands => do
    let (values, memory, _) ← Veir.CTree.interpretOp' (op.getOpType! ctx)
      (op.getProperties! ctx (op.getOpType! ctx)) (op.getResultTypes! ctx)
      operands.toArray #[] memory
    next (resolve.setResultsDefault op values) memory

/-- Existing operations have the same raw interpretation after allocating more operations. -/
theorem interpretCreatedOp_withCreatedOps {ctx ctx' : WfIRContext OpCode}
    (h : Veir.WfIRContext.WithCreatedOps ctx ctx') (op : OperationPtr) (hop : op.InBounds ctx.raw)
    (resolve : ValueResolver) (memory : MemoryState) (next : ValueResolver → MemoryState → Tree α) :
    interpretCreatedOp ctx.raw op resolve memory next = interpretCreatedOp ctx'.raw op resolve memory next := by
  obtain ⟨hc, ht, ho, hp⟩ := WfIRContext.WithCreatedOps.operation_fields h op hop
  unfold interpretCreatedOp
  rw [hc, ht, ho, hp]

/-- Interpret the actual returned operations in their final concrete context. -/
@[expose]
def interpretCreatedOps (ctx : IRContext OpCode) (ops : List OperationPtr)
    (resolve : ValueResolver) (memory : MemoryState) (next : ValueResolver → MemoryState → Tree α) : Tree α :=
  match ops with
  | [] => next resolve memory
  | op :: ops => interpretCreatedOp ctx op resolve memory fun r m => interpretCreatedOps ctx ops r m next

/-- Allocate one real creation declaration, then interpret the operation it actually returned. -/
@[expose]
def CreateDecl.executeSemantics (decl : CreateDecl OpCode) (ctx : WfIRContext OpCode)
    (a : Assignment OpCode) (resolve : ValueResolver) (memory : MemoryState)
    (next : WfIRContext OpCode → Assignment OpCode → ValueResolver → MemoryState → Tree α) : Tree α :=
  match decl.run a ctx with
  | none => fail
  | some (newCtx, newOps, b) =>
    match newOps[0]? with
    | none => next newCtx b resolve memory
    | some op => interpretCreatedOp newCtx.raw op resolve memory (next newCtx b)

/-- A successful allocation step has exactly the symbolic creation semantics.
This theorem concerns raw opcode results; checked result conformance is a separate obligation. -/
theorem CreateDecl.executeSemantics_eq
    (decl : CreateDecl OpCode) {ctx newCtx : WfIRContext OpCode}
    {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (resolve : ValueResolver) (memory : MemoryState)
    (next : SemanticAssignment → MemoryState → Tree α)
    (hbound : a.ValuesInBounds ctx.raw)
    (h : decl.run a ctx = some (newCtx, newOps, b)) :
    CreateDecl.executeSemantics decl ctx a resolve memory (fun ctx b r m => next (b.denote r (fun p => p.getType! ctx.raw)) m) =
      CreateDecl.semantics decl (a.denote resolve (fun p => p.getType! ctx.raw)) memory next := by
  cases decl with
  | operation code operandHandles typeHandles propertyHandle opHandle resultHandles =>
    have hrun := h
    simp only [Veir.Puddle.CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨operands, hop, types, hty, properties, hprop, u, hguard, h⟩ := h
    split at h
    · rename_i hin
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨createdCtx, op⟩, hcreate, bound, hbindop, final, hbindresults, heq⟩ := h
      cases heq
      have hfields := createOp_semantic_fields hcreate
      have hfresh := WfRewriter.createOp_new_not_inBounds op hcreate
      have hraw (args : Array RuntimeValue) (mem : MemoryState) :
          Veir.CTree.interpretOp' (op.getOpType! createdCtx.raw)
            (op.getProperties! createdCtx.raw (op.getOpType! createdCtx.raw)) types args #[] mem =
          Veir.CTree.interpretOp' code properties types args #[] mem := by
        rw [hfields.1, hfields.2.2.2]
      simp only [CreateDecl.executeSemantics, hrun, (show (#[op][0]? : Option OperationPtr) = some op from rfl),
        interpretCreatedOp, hfields.2.1, hfields.2.2.1, hraw,
        CreateDecl.semantics, Assignment.denote_getValues, Assignment.denote_getTypes,
        Assignment.denote_getProperty, hop, hty, hprop, Option.bind_eq_bind,
        Option.bind_some, Option.map_some]
      cases hoperands : operands.toList.mapM resolve with
      | none => rfl
      | some args =>
        simp only [Array.toArray_toList]
        congr 1
        funext result
        rcases result with ⟨values, memory', action⟩
        have htype : ∀ (pointer : ValuePtr), pointer.InBounds ctx.raw →
            pointer.getType! createdCtx.raw = pointer.getType! ctx.raw := by
          intro pointer hp
          have ht := ValuePtr.getType!_WfRewriter_createOp hcreate (value := pointer)
          cases pointer with
          | blockArgument => exact ht
          | opResult result =>
            have hne : result.op ≠ op := by grind
            simpa [hne] using ht
        have hbound := Assignment.denote_bindFreshOpResultsDefault_typed resolve values
          hbindop hbindresults hbound hfresh htype
        simp only [hfields.2.1] at hbound
        rw [hbound]
    · contradiction
  | type value result =>
    have hmeta := CreateDecl.semantics_of_run_metadata (.type value result) resolve memory next trivial h (fun p => p.getType! ctx.raw)
    rcases hmeta with ⟨rfl, rfl, hsem⟩
    simpa only [CreateDecl.executeSemantics, h, Array.getElem?_empty] using hsem.symm
  | property code value result =>
    have hmeta := CreateDecl.semantics_of_run_metadata (.property code value result) resolve memory next trivial h (fun p => p.getType! ctx.raw)
    rcases hmeta with ⟨rfl, rfl, hsem⟩
    simpa only [CreateDecl.executeSemantics, h, Array.getElem?_empty] using hsem.symm
  | applyNative inputs rewrite outputs =>
    have hmeta := CreateDecl.semantics_of_run_metadata (.applyNative inputs rewrite outputs) resolve memory next trivial h (fun p => p.getType! ctx.raw)
    rcases hmeta with ⟨rfl, rfl, hsem⟩
    simpa only [CreateDecl.executeSemantics, h, Array.getElem?_empty] using hsem.symm

/-- Runtime execution fixes the concrete context and assignment passed to the continuation. -/
theorem CreateDecl.executeSemantics_congr_of_run
    {decl : CreateDecl OpCode} {ctx newCtx : WfIRContext OpCode}
    {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (resolve : ValueResolver) (memory : MemoryState)
    (next next' : WfIRContext OpCode → Assignment OpCode → ValueResolver → MemoryState → Tree α)
    (h : decl.run a ctx = some (newCtx, newOps, b))
    (hnext : ∀ r m, next newCtx b r m = next' newCtx b r m) :
    CreateDecl.executeSemantics decl ctx a resolve memory next =
      CreateDecl.executeSemantics decl ctx a resolve memory next' := by
  simp only [CreateDecl.executeSemantics, h]
  have heq : next newCtx b = next' newCtx b := by funext r m; exact hnext r m
  rw [heq]

/-- Run allocations in program order and interpret their concrete operations as they are created. -/
@[expose]
def CreateProg.executeDecls (decls : List (CreateDecl OpCode)) (ctx : WfIRContext OpCode)
    (a : Assignment OpCode) (resolve : ValueResolver) (memory : MemoryState)
    (next : WfIRContext OpCode → Assignment OpCode → ValueResolver → MemoryState → Tree α) : Tree α :=
  match decls with
  | [] => next ctx a resolve memory
  | decl :: decls => CreateDecl.executeSemantics decl ctx a resolve memory fun ctx a resolve memory =>
      CreateProg.executeDecls decls ctx a resolve memory next

/-- Every successfully executed creation list implements its symbolic CPS semantics. -/
theorem CreateProg.executeDecls_eq
    (decls : List (CreateDecl OpCode)) {ctx newCtx : WfIRContext OpCode}
    {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (resolve : ValueResolver) (memory : MemoryState)
    (next : SemanticAssignment → MemoryState → Tree α)
    (hbound : a.ValuesInBounds ctx.raw)
    (h : Veir.Puddle.CreateProg.runDecls decls ctx a = some (newCtx, newOps, b)) :
    CreateProg.executeDecls decls ctx a resolve memory (fun ctx b r m => next (b.denote r (fun p => p.getType! ctx.raw)) m) =
      CreateProg.semanticsDecls decls (a.denote resolve (fun p => p.getType! ctx.raw)) memory next := by
  induction decls generalizing ctx a newOps resolve memory with
  | nil => rfl
  | cons decl decls ih =>
    simp only [Veir.Puddle.CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨middleCtx, created, middle⟩, hd, ⟨finalCtx, restOps, final⟩, hr, heq⟩ := h
    cases heq
    have hmiddle := Veir.Puddle.CreateDecl.valuesInBounds_of_run decl hbound hd
    unfold CreateProg.executeDecls
    calc
      _ = CreateDecl.executeSemantics decl ctx a resolve memory
          (fun ctx b r m => CreateProg.semanticsDecls decls (b.denote r (fun p => p.getType! ctx.raw)) m next) := by
        apply CreateDecl.executeSemantics_congr_of_run resolve memory _ _ hd
        intro r m
        exact ih r m hmiddle hr
      _ = _ := CreateDecl.executeSemantics_eq decl resolve memory
        (fun s m => CreateProg.semanticsDecls decls s m next) hbound hd

/-- Concrete allocation-order execution equals interpreting exactly the returned operations
in the final context. -/
theorem CreateProg.executeDecls_eq_returnedOps
    (decls : List (CreateDecl OpCode)) {ctx newCtx : WfIRContext OpCode}
    {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (resolve : ValueResolver) (memory : MemoryState)
    (next : Assignment OpCode → ValueResolver → MemoryState → Tree α)
    (h : Veir.Puddle.CreateProg.runDecls decls ctx a = some (newCtx, newOps, b)) :
    CreateProg.executeDecls decls ctx a resolve memory (fun _ => next) =
      interpretCreatedOps newCtx.raw newOps.toList resolve memory (next b) := by
  induction decls generalizing ctx a newOps resolve memory with
  | nil =>
    simp only [Veir.Puddle.CreateProg.runDecls, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | cons decl decls ih =>
    simp only [Veir.Puddle.CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨middleCtx, created, middle⟩, hd, ⟨finalCtx, restOps, final⟩, hr, heq⟩ := h
    cases heq
    have hctx := Veir.Puddle.CreateProg.runDecls_withCreatedOps _ _ _ _ _ _ hr
    unfold CreateProg.executeDecls
    calc
      _ = CreateDecl.executeSemantics decl ctx a resolve memory
          (fun _ _ r m => interpretCreatedOps finalCtx.raw restOps.toList r m (next final)) := by
        apply CreateDecl.executeSemantics_congr_of_run resolve memory _ _ hd
        intro r m
        exact ih r m hr
      _ = _ := by
        simp only [CreateDecl.executeSemantics, hd]
        rcases Veir.Puddle.CreateDecl.run_ops_shape decl hd with hempty | ⟨op, hsingle, hop⟩
        · rw [hempty]
          simp
        · rw [hsingle]
          simp only [(show (#[op][0]? : Option OperationPtr) = some op from rfl),
            Array.toList_append, List.cons_append, List.nil_append,
            interpretCreatedOps]
          exact interpretCreatedOp_withCreatedOps hctx op hop resolve memory _

/-- Read final replacement values through their actual SSA pointers. -/
@[expose]
def CreateProg.executeSemantics (prog : Veir.Puddle.CreateProg OpCode β)
    (replacement : Replacement OpCode) (ctx : WfIRContext OpCode) (a : Assignment OpCode)
    (resolve : ValueResolver) (memory : MemoryState) :
    Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  CreateProg.executeDecls prog.decls ctx a resolve memory fun _ final resolve memory =>
    match final.getValues replacement.values >>= fun pointers => pointers.toList.mapM resolve with
    | some values => pure (values.toArray, memory, none)
    | none => fail

/-- A successful `CreateProg.run` has the symbolic program's raw CTree semantics. -/
theorem CreateProg.executeSemantics_eq
    (prog : Veir.Puddle.CreateProg OpCode β) (replacement : Replacement OpCode)
    {ctx newCtx : WfIRContext OpCode} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (resolve : ValueResolver) (memory : MemoryState) (hbound : a.ValuesInBounds ctx.raw)
    (h : prog.run a ctx = some (newCtx, newOps, b)) :
    CreateProg.executeSemantics prog replacement ctx a resolve memory =
      CreateProg.semantics prog replacement (a.denote resolve (fun p => p.getType! ctx.raw)) memory := by
  unfold CreateProg.executeSemantics CreateProg.semantics
  have hnext : (fun (_ : WfIRContext OpCode) (final : Assignment OpCode) (r : ValueResolver) m =>
      match final.getValues replacement.values >>= fun pointers => pointers.toList.mapM r with
      | some values => (pure (values.toArray, m, none) : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
      | none => fail) =
      (fun ctx final r m =>
        match (final.denote r (fun p => p.getType! ctx.raw)).getValues replacement.values.toList with
        | some values => pure (values.toArray, m, none)
        | none => fail) := by
    funext ctx final r m
    rw [Assignment.denote_getValues _ _ _ (fun p => p.getType! ctx.raw)]
  rw [hnext]
  exact CreateProg.executeDecls_eq prog.decls resolve memory
    (fun final m => match final.getValues replacement.values.toList with
      | some values => pure (values.toArray, m, none)
      | none => fail) hbound h

/-- The symbolic creation tree is exactly interpretation of the actual returned operations in
its final IR context, followed by concrete replacement-pointer resolution. -/
theorem CreateProg.semantics_eq_returnedOps
    (prog : Veir.Puddle.CreateProg OpCode β) (replacement : Replacement OpCode)
    {ctx newCtx : WfIRContext OpCode} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (resolve : ValueResolver) (memory : MemoryState) (hbound : a.ValuesInBounds ctx.raw)
    (h : prog.run a ctx = some (newCtx, newOps, b)) :
    CreateProg.semantics prog replacement (a.denote resolve (fun p => p.getType! ctx.raw)) memory =
      interpretCreatedOps newCtx.raw newOps.toList resolve memory (fun r m =>
        match b.getValues replacement.values >>= fun pointers => pointers.toList.mapM r with
        | some values => pure (values.toArray, m, none)
        | none => fail) := by
  rw [← CreateProg.executeSemantics_eq prog replacement resolve memory hbound h]
  exact CreateProg.executeDecls_eq_returnedOps prog.decls resolve memory
    (fun final r m =>
      match final.getValues replacement.values >>= fun pointers => pointers.toList.mapM r with
      | some values => pure (values.toArray, m, none)
      | none => fail) h

end CTree

end

end Veir.Puddle
