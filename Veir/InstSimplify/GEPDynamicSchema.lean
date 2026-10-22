import Veir.InstSimplify.GEPZeroSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- One freely typed scalar dynamic index per slot; construction arity is arbitrary. -/
def matchGEPDynamicIndices : Nat → MatchProg.Builder (Array (Handle OpCode .value))
  | 0 => pure #[]
  | n + 1 => do
    let ty ← MatchProg.type (Attr := IntegerType)
    let index ← MatchProg.value ty
    let indices ← matchGEPDynamicIndices n
    return #[index] ++ indices

/-- Declarations in binding order for freely typed scalar GEP indices. -/
def gepDynamicDecls (start : Nat) : Nat → List (MatchDecl OpCode)
  | 0 => []
  | n + 1 =>
    .type (fun ty => ((ty.cast? IntegerType).map (fun _ => true)).getD false) ⟨start⟩ ::
    .value ⟨start⟩ ⟨start + 1⟩ :: gepDynamicDecls (start + 2) n

def gepDynamicHandles (start : Nat) : Nat → Array (Handle OpCode .value)
  | 0 => #[]
  | n + 1 => #[⟨start + 1⟩] ++ gepDynamicHandles (start + 2) n

theorem matchGEPDynamicIndices_run (n : Nat) (state : MatchProg.BuilderState) :
    (matchGEPDynamicIndices n).run state =
      (gepDynamicHandles state.nextId n,
       { state with
         nextId := state.nextId + 2 * n
         decls := (gepDynamicDecls state.nextId n).reverse ++ state.decls}) := by
  induction n generalizing state with
  | zero => simp [matchGEPDynamicIndices, gepDynamicHandles, gepDynamicDecls, pure]
  | succ n ih =>
    simp [matchGEPDynamicIndices, MatchProg.type, MatchProg.value, bind, pure, ih,
      gepDynamicHandles, gepDynamicDecls, List.append_assoc]
    omega

theorem gepDynamicHandles_bounds (start n : Nat) (handle : Handle OpCode .value)
    (h : handle ∈ gepDynamicHandles start n) :
    start ≤ handle.id ∧ handle.id < start + 2 * n := by
  induction n generalizing start with
  | zero => simp [gepDynamicHandles] at h
  | succ n ih =>
    simp only [gepDynamicHandles, Array.mem_append, Array.mem_singleton] at h
    rcases h with rfl | h
    · simp; omega
    · have hb := ih (start+2) h
      omega

theorem gep_modelsDecls_append (xs ys : List (MatchDecl OpCode)) (assignment : SemanticAssignment)
    (k : SemanticAssignment → Prop) :
    MatchProg.modelsDecls (xs ++ ys) assignment k =
      MatchProg.modelsDecls xs assignment (fun a => MatchProg.modelsDecls ys a k) := by
  induction xs generalizing assignment with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, MatchProg.modelsDecls]; simp only [ih]

/-- An arbitrary number of typed binders resolves to a runtime-value list while
preserving every binding allocated before the block. This CPS interface is
independent of the GEP rule and is reusable for other variadic schemas. -/
theorem gepDynamicDecls_models (start n : Nat) (assignment : SemanticAssignment)
    (k : SemanticAssignment → Prop)
    (hk : ∀ final values,
      final.getValues (gepDynamicHandles start n).toList = some values →
      (∀ id, id < start → final id = assignment id) → k final) :
    MatchProg.modelsDecls (gepDynamicDecls start n) assignment k := by
  induction n generalizing start assignment k with
  | zero =>
    apply hk assignment []
    · rfl
    · simp
  | succ n ih =>
    simp only [gepDynamicDecls, MatchProg.modelsDecls, MatchDecl.Models]
    intro ty hty
    simp only [SemanticAssignment.getType, SemanticAssignment.bindType,
      SemanticAssignment.bind, ↓reduceIte]
    intro value hvalue
    apply ih
    intro final values hvalues heq
    apply hk final (value :: values)
    · have hv : final.getValue ⟨start+1⟩ = some value := by
        unfold SemanticAssignment.getValue
        rw [heq (start+1) (by omega)]
        simp [SemanticAssignment.bindValue, SemanticAssignment.bind]
      change List.mapM final.getValue _ = some values at hvalues
      simp [gepDynamicHandles, SemanticAssignment.getValues, hv, hvalues]
    · intro id hid
      rw [heq id (by omega)]
      simp [SemanticAssignment.bindValue, SemanticAssignment.bindType,
        SemanticAssignment.bind, show id ≠ start+1 by omega, show id ≠ start by omega]

theorem gep_lookup_cons (ctx : HandleContext) (id : Nat) (kind : HandleType OpCode) (query : Nat) :
    ({ctx with bindings := (id,kind) :: ctx.bindings} : HandleContext).lookup query =
      if id = query then some kind else ctx.lookup query := rfl

theorem gep_lookup_prefix (bindings : List (Nat × HandleType OpCode)) (unavailable : List Nat)
    (id : Nat) (kind : HandleType OpCode) (query : Nat) :
    (HandleContext.mk ((id,kind) :: bindings) unavailable).lookup query =
      if id = query then some kind else (HandleContext.mk bindings unavailable).lookup query := rfl

def gepFreshFrom (ctx : HandleContext) (start : Nat) : Prop :=
  ∀ id, start ≤ id → ctx.lookup id = none

/-- Structural counterpart of the CPS binder lemma: every declared value is
available, earlier bindings are preserved, and the remaining suffix is fresh. -/
theorem gepDynamicDecls_collect (start n : Nat) (ctx : HandleContext)
    (hu : ctx.unavailable = []) (hf : gepFreshFrom ctx start) :
    ∃ final, MatchProg.collectDeclBindings (gepDynamicDecls start n) ctx = some final ∧
      final.unavailable = [] ∧ gepFreshFrom final (start + 2*n) ∧
      (∀ id, id < start → final.lookup id = ctx.lookup id) ∧
      (∀ handle ∈ gepDynamicHandles start n, final.require handle = true) := by
  induction n generalizing start ctx with
  | zero =>
    refine ⟨ctx, rfl, hu, ?_, ?_, ?_⟩
    · simpa using hf
    · simp
    · simp [gepDynamicHandles]
  | succ n ih =>
    let step : HandleContext :=
      { bindings := (start+1,.value) :: (start,.type) :: ctx.bindings
        unavailable := ctx.unavailable }
    have hs : gepFreshFrom step (start+2) := by
      intro id hid
      simp only [step, gep_lookup_cons]
      simp [gep_lookup_prefix, show start+1 ≠ id by omega,
        show start ≠ id by omega, hf id (by omega)]
    obtain ⟨final,hcollect,hu',hf',hold,hvalues⟩ := ih (start+2) step hu hs
    refine ⟨final, ?_, hu', ?_, ?_, ?_⟩
    · have ht : ctx.lookup start = none := hf _ (by omega)
      have hv : ctx.lookup (start+1) = none := hf _ (by omega)
      have hctx : (HandleContext.mk ctx.bindings []) = ctx := by
        cases ctx; simp_all
      simpa [gepDynamicDecls, MatchProg.collectDeclBindings, MatchDecl.collectBindings,
        HandleContext.insertFresh, HandleContext.require, gep_lookup_prefix, ht, hv, hu,
        step, hctx, guard, pure, bind] using hcollect
    · have he : start + 2 * (n+1) = start+2+2*n := by omega
      rw [he]
      exact hf'
    · intro id hid
      rw [hold id (by omega)]
      simp [step, gep_lookup_prefix, show start+1 ≠ id by omega, show start ≠ id by omega]
    · intro handle hm
      simp only [gepDynamicHandles, Array.mem_append, Array.mem_singleton] at hm
      rcases hm with rfl | hm
      · simp [HandleContext.require, hu', hold (start+1) (by omega), step, gep_lookup_prefix]
      · exact hvalues handle hm

def gepDynamicRawCount (n : Nat) : PropertyMatcher (.llvm .getelementptr : OpCode) :=
  fun props => (props.rawConstantIndices.values.filter (· == -2147483648)).size == n

/-- Poison-base GEP with every finite dynamic-operand arity, arbitrary static/dynamic raw metadata. -/
def gepPoisonBaseFamily (n : Nat) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType)
    let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let indices ← matchGEPDynamicIndices n
    let _ ← MatchProg.root (.llvm .getelementptr) (#[poison.res[0]!] ++ indices) #[ty]
      (gepDynamicRawCount n)
    return poison.res[0]!)
  pure (fun p => p)

/-- Explicit normal form of the builder, used only to prove its checker obligations. -/
def gepPoisonBaseCore (n : Nat) : Pattern OpCode where
  Exports := Handle OpCode .value
  matcher := {
    rootHandle := ⟨4 + 2*n⟩
    numHandles := 4 + 2*n + 1 + 2
    exports := ⟨2⟩
    decls := .operation (.llvm .getelementptr) (#[⟨2⟩] ++ gepDynamicHandles 4 n) #[⟨0⟩]
      (gepDynamicRawCount n)
      ⟨4 + 2*n + 1 + 1⟩ ⟨4 + 2*n⟩ #[⟨4 + 2*n + 1⟩] rfl ::
      (gepDynamicDecls 4 n).reverse ++
      [.operation (.llvm .mlir__poison) #[] #[⟨0⟩] (fun _ => true) ⟨3⟩ ⟨1⟩ #[⟨2⟩] rfl,
       .type (fun ty => ((ty.cast? LLVM.PointerType).map (fun _ => true)).getD false) ⟨0⟩]
  }
  CreationExports := Handle OpCode .value
  creation := { decls := [], numHandles := 4 + 2*n + 1 + 2, exports := ⟨2⟩ }
  replacement := { values := #[⟨2⟩] }

theorem gepPoisonBaseFamily_eq (n : Nat) : gepPoisonBaseFamily n = gepPoisonBaseCore n := by
  unfold gepPoisonBaseFamily
  unfoldPuddleBuilder
  simp only [matchGEPDynamicIndices_run]
  unfoldPuddleBuilder
  simp [gepPoisonBaseCore, show Array.range 1 = #[0] by decide]

abbrev gepStructuralDecl : MatchDecl OpCode → Bool
  | @MatchDecl.applyNative _ _ _ _ _ _ => false
  | @MatchDecl.inspectOperation _ _ _ _ _ _ _ => false
  | _ => true

theorem gepDynamicDecls_filter (start n : Nat) :
    (gepDynamicDecls start n).filter gepStructuralDecl = gepDynamicDecls start n ∧
    (gepDynamicDecls start n).filter (fun d => !gepStructuralDecl d) = [] := by
  induction n generalizing start with
  | zero => simp [gepDynamicDecls]
  | succ n ih => simpa [gepDynamicDecls, gepStructuralDecl] using ih (start+2)

theorem gepDynamicDecls_filter_true (start n : Nat) (p : MatchDecl OpCode → Bool)
    (ht : ∀ m h, p (.type m h) = true) (hv : ∀ t v, p (.value t v) = true) :
    (gepDynamicDecls start n).filter p = gepDynamicDecls start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [gepDynamicDecls, ht, hv, ih]

theorem gepDynamicDecls_filter_false (start n : Nat) (p : MatchDecl OpCode → Bool)
    (ht : ∀ m h, p (.type m h) = false) (hv : ∀ t v, p (.value t v) = false) :
    (gepDynamicDecls start n).filter p = [] := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [gepDynamicDecls, ht, hv, ih]

theorem gepPoisonBaseCore_bindingDecls (n : Nat) :
    (gepPoisonBaseCore n).matcher.bindingDecls =
      [.type (fun ty => ((ty.cast? LLVM.PointerType).map (fun _ => true)).getD false) ⟨0⟩,
       .operation (.llvm .mlir__poison) #[] #[⟨0⟩] (fun _ => true) ⟨3⟩ ⟨1⟩ #[⟨2⟩] rfl] ++
       gepDynamicDecls 4 n ++
      [.operation (.llvm .getelementptr) (#[⟨2⟩] ++ gepDynamicHandles 4 n) #[⟨0⟩]
        (gepDynamicRawCount n)
        ⟨4+2*n+1+1⟩ ⟨4+2*n⟩ #[⟨4+2*n+1⟩] rfl] := by
  simp only [MatchProg.bindingDecls, gepPoisonBaseCore, List.partition_eq_filter_filter,
    List.filter_cons, List.filter_append, List.filter_reverse]
  rw [gepDynamicDecls_filter_true _ _ _ (by intros; rfl) (by intros; rfl)]
  rw [gepDynamicDecls_filter_false _ _ _ (by intros; rfl) (by intros; rfl)]
  simp [List.reverse_append, List.append_assoc]

theorem gepDynamicDecls_supported (start n : Nat) :
    ∀ d ∈ gepDynamicDecls start n, d.Supported := by
  induction n generalizing start with
  | zero => simp [gepDynamicDecls]
  | succ n ih =>
    intro d hd
    simp only [gepDynamicDecls, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · trivial
    · trivial
    · exact ih (start+2) d hd

theorem gepPoisonBaseCore_supported (n : Nat) : (gepPoisonBaseCore n).Supported := by
  constructor
  · intro d hd
    simp only [gepPoisonBaseCore, List.mem_cons, List.mem_append, List.mem_reverse,
      List.not_mem_nil, or_false] at hd
    rcases hd with (rfl | hd) | rfl | rfl
    · simp [MatchDecl.Supported, SupportedOpCode, get_effects, is_terminator]
    · exact gepDynamicDecls_supported 4 n d hd
    · simp [MatchDecl.Supported, SupportedOpCode, get_effects, is_terminator]
    · trivial
  · simp [CreateProg.Supported, gepPoisonBaseCore]

theorem gep_collectDeclBindings_append (xs ys : List (MatchDecl OpCode)) (ctx : HandleContext) :
    MatchProg.collectDeclBindings (xs ++ ys) ctx =
      (MatchProg.collectDeclBindings xs ctx).bind (MatchProg.collectDeclBindings ys) := by
  induction xs generalizing ctx with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, MatchProg.collectDeclBindings]
    cases h : x.collectBindings ctx <;> simp [h, ih]

theorem gep_lookup_empty (unavailable : List Nat) (id : Nat) :
    (HandleContext.mk [] unavailable).lookup id = none := rfl

theorem gep_lookup_clear_unavailable (bindings : List (Nat × HandleType OpCode))
    (unavailable : List Nat) (id : Nat) :
    (HandleContext.mk bindings unavailable).lookup id =
      (HandleContext.mk bindings []).lookup id := rfl

def gepInitialContext : HandleContext :=
  ⟨[(1,.op),(3,.prop (.llvm .mlir__poison)),(2,.value),(0,.type)],[]⟩

theorem gepPoisonBaseCore_structure (n : Nat) : (gepPoisonBaseCore n).StructurallyWellFormed := by
  have hi : gepFreshFrom gepInitialContext 4 := by
    intro id hid
    simp [gepInitialContext, gep_lookup_prefix, gep_lookup_empty,
      show 1 ≠ id by omega, show 3 ≠ id by omega,
      show 2 ≠ id by omega, show 0 ≠ id by omega]
  obtain ⟨ctx,hc,hu,hf,hold,hvalues⟩ := gepDynamicDecls_collect 4 n gepInitialContext rfl hi
  have h0 : ctx.lookup 0 = some .type := by rw [hold 0 (by omega)]; rfl
  have h2 : ctx.lookup 2 = some .value := by rw [hold 2 (by omega)]; rfl
  have hindices : (gepDynamicHandles 4 n).toList.all ctx.require = true := by
    apply List.all_eq_true.mpr
    intro handle hm
    exact hvalues handle (by simpa using hm)
  have hoperands : ctx.requireMany ((#[⟨2⟩] : Array (Handle OpCode .value)) ++ gepDynamicHandles 4 n).toList = true := by
    simp [HandleContext.requireMany, HandleContext.require, hu, h2, hindices]
  have hiLookup : ∀ (i : Nat) (h : i < (gepDynamicHandles 4 n).size),
      ctx.lookup (gepDynamicHandles 4 n)[i].id = some .value := by
    intro i h
    have hv := hvalues (gepDynamicHandles 4 n)[i] (Array.getElem_mem h)
    simpa [HandleContext.require, hu] using hv
  have hr := hf (4+2*n) (by omega)
  have hv := hf (4+2*n+1) (by omega)
  have hp := hf (4+2*n+1+1) (by omega)
  have hend : (HandleContext.mk ctx.bindings []) = ctx := by cases ctx; simp_all
  simp only [Pattern.StructurallyWellFormed, Pattern.checkStructure, MatchProg.collectBindings,
    gepPoisonBaseCore_bindingDecls, gep_collectDeclBindings_append]
  simp only [gepPoisonBaseCore, MatchProg.rootResults?, List.cons_append, ↓reduceIte,
    CreateProg.checkBindings, Replacement.checkBindings, List.foldlM_nil]
  have hprefix : MatchProg.collectDeclBindings
      [.type (fun ty => ((ty.cast? LLVM.PointerType).map (fun _ => true)).getD false) ⟨0⟩,
       .operation (.llvm .mlir__poison) #[] #[⟨0⟩] (fun _ => true) ⟨3⟩ ⟨1⟩ #[⟨2⟩] rfl]
      HandleContext.empty = some gepInitialContext := by rfl
  simp only [hprefix, bind, pure, Option.bind_some]
  rw [hc]
  simp [MatchProg.collectDeclBindings, MatchDecl.collectBindings, HandleContext.insertManyFresh,
    HandleContext.insertFresh, HandleContext.requireMany, HandleContext.require,
    HandleContext.forbidMany, HandleContext.forbid, gep_lookup_prefix,
    hr, hv, hp, hu, h0, h2, hend, hoperands, hiLookup, guard, pure, bind,
    gep_lookup_clear_unavailable,
    show 4+2*n ≠ 1 by omega, show 2 ≠ 4+2*n by omega,
    show 4+2*n+1+1 ≠ 4+2*n by omega,
    show 4+2*n+1 ≠ 4+2*n by omega,
    show 4+2*n+1 ≠ 4+2*n+1+1 by omega,
    show 4+2*n+1+1 ≠ 4+2*n+1 by omega,
    show 4+2*n ≠ 2 by omega,
    show 4+2*n+1 ≠ 2 by omega,
    show 4+2*n+1+1 ≠ 2 by omega]

theorem gepPoisonBaseCore_semantics (n : Nat) : (gepPoisonBaseCore n).PreservesSemantics := by
  simp only [Pattern.PreservesSemantics, MatchProg.Models,
    gepPoisonBaseCore_bindingDecls, gep_modelsDecls_append]
  simpPuddleSemantics
  rintro ⟨⟩ props poison hp
  obtain rfl := (ptr_poison_iff props poison).mp hp
  apply gepDynamicDecls_models
  intro final values hvalues heq
  have h0 : final 0 = some (.type (LLVM.PointerType.mk : TypeAttr)) := by
    rw [heq 0 (by omega)]; rfl
  have hb2 : final 2 = some (.value (.addr .poison)) := by
    rw [heq 2 (by omega)]; rfl
  have h2 : final.getValue ⟨2⟩ = some (.addr .poison) := by
    simp [SemanticAssignment.getValue, hb2]
  change List.mapM final.getValue _ = some values at hvalues
  simp only [Array.toList_append, List.cons_append, List.nil_append, List.mapM_cons,
    h2, hvalues, h0, Option.bind_some]
  intro props value hcount hi
  have hi' : InterpretsTo (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)]
      (#[.addr .poison] ++ values.toArray) #[value] := by simpa using hi
  obtain rfl := gep_poison_base_refines props values.toArray value hi'
  simp [gepPoisonBaseCore, CreateProg.modelsDecls, SemanticAssignment.getValue,
    SemanticAssignment.bind, hb2,
    show 4+2*n+1 ≠ 4+2*n+1+1 by omega,
    show 2 ≠ 4+2*n+1 by omega,
    show 2 ≠ 4+2*n+1+1 by omega,
    RuntimeValue.arrayIsRefinedBy_refl]

theorem gepPoisonBaseFamily_valid (n : Nat) : Pattern.Valid (gepPoisonBaseFamily n) := by
  rw [gepPoisonBaseFamily_eq]
  exact ⟨gepPoisonBaseCore_supported n, rfl, gepPoisonBaseCore_structure n,
    gepPoisonBaseCore_semantics n⟩

end Veir.InstSimplify
