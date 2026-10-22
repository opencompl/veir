import Veir.InstSimplify.GEPDynamicSchema
import Veir.InstSimplify.GEPZeroInterp
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

def gepZeroTypeGuard (payload : Int) (ty : TypeAttr) : Bool :=
  ((ty.cast? IntegerType).map (fun t => BitVec.ofInt t.bitwidth payload == 0)).getD false

def matchGEPZeroIndices : List Int → MatchProg.Builder (Array (Handle OpCode .value))
  | [] => pure #[]
  | payload :: payloads => do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => BitVec.ofInt t.bitwidth payload == 0)
    let index ← matchIntConstant ty payload
    let indices ← matchGEPZeroIndices payloads
    return #[index] ++ indices

def gepZeroDecls (start : Nat) : List Int → List (MatchDecl OpCode)
  | [] => []
  | payload :: payloads =>
    .type (gepZeroTypeGuard payload) ⟨start⟩ ::
    .operation (.llvm .mlir__constant) #[] #[⟨start⟩] (fun p => intConstantGuard p payload)
      ⟨start+3⟩ ⟨start+1⟩ #[⟨start+2⟩] rfl :: gepZeroDecls (start+4) payloads

def gepZeroHandles (start : Nat) : List Int → Array (Handle OpCode .value)
  | [] => #[]
  | _ :: payloads => #[⟨start+2⟩] ++ gepZeroHandles (start+4) payloads

theorem matchGEPZeroIndices_run (payloads : List Int) (state : MatchProg.BuilderState) :
    (matchGEPZeroIndices payloads).run state =
      (gepZeroHandles state.nextId payloads,
       {state with nextId := state.nextId + 4 * payloads.length
                   decls := (gepZeroDecls state.nextId payloads).reverse ++ state.decls}) := by
  induction payloads generalizing state with
  | nil => simp [matchGEPZeroIndices, gepZeroHandles, gepZeroDecls, pure]
  | cons p ps ih =>
    simp [matchGEPZeroIndices, MatchProg.type, matchIntConstant, MatchProg.operation,
      bind, pure, ih, gepZeroHandles, gepZeroDecls, gepZeroTypeGuard, List.append_assoc,
      show Array.range 1 = #[0] by decide]
    constructor
    · omega
    · rfl

theorem gepZeroHandles_bounds (start : Nat) (payloads : List Int) (handle : Handle OpCode .value)
    (h : handle ∈ gepZeroHandles start payloads) :
    start ≤ handle.id ∧ handle.id < start + 4 * payloads.length := by
  induction payloads generalizing start with
  | nil => simp [gepZeroHandles] at h
  | cons p ps ih =>
    simp only [gepZeroHandles, Array.mem_append, Array.mem_singleton] at h
    rcases h with rfl | h
    · simp; omega
    · have hb := ih (start+4) h
      simp only [List.length_cons] at *
      omega

theorem gepZeroDecls_models (start : Nat) (payloads : List Int) (assignment : SemanticAssignment)
    (k : SemanticAssignment → Prop)
    (hk : ∀ final values,
      final.getValues (gepZeroHandles start payloads).toList = some values →
      values.length = payloads.length →
      (∀ v ∈ values, GEPValueZero v) →
      (∀ id, id < start → final id = assignment id) → k final) :
    MatchProg.modelsDecls (gepZeroDecls start payloads) assignment k := by
  induction payloads generalizing start assignment k with
  | nil =>
    apply hk assignment []
    · rfl
    · rfl
    · simp
    · simp
  | cons payload payloads ih =>
    simp only [gepZeroDecls, MatchProg.modelsDecls, MatchDecl.Models]
    intro ty hty
    cases hc : ty.cast? IntegerType with
    | none => simp [gepZeroTypeGuard, hc] at hty
    | some it =>
      have hety : TypeAttr.of IntegerType it = ty := (IsTypeAttr.cast?_eq_some_iff ty it).mp hc
      subst ty
      have hz : BitVec.ofInt it.bitwidth payload = 0#it.bitwidth := by
        simpa [gepZeroTypeGuard, IsTypeAttr.cast?_of] using hty
      simp only [SemanticAssignment.getValues, SemanticAssignment.getTypes, SemanticAssignment.getType,
        SemanticAssignment.bindType, SemanticAssignment.bind, List.mapM_nil, List.mapM_cons,
        Option.bind_some, SemanticAssignment.ForallValues, ↓reduceIte]
      intro props value hp hi
      obtain rfl := (matched_constant_iff it props payload hp value).mp hi
      apply ih
      intro final values hvalues hlen hzero heq
      apply hk final (.int it.bitwidth (.val (BitVec.ofInt it.bitwidth payload)) :: values)
      · have hv : final.getValue ⟨start+2⟩ = some (.int it.bitwidth (.val (BitVec.ofInt it.bitwidth payload))) := by
          unfold SemanticAssignment.getValue
          rw [heq (start+2) (by omega)]
          simp [SemanticAssignment.bindProperty, SemanticAssignment.bindValue, SemanticAssignment.bind,
            show start+3 ≠ start+2 by omega]
        change List.mapM final.getValue _ = some values at hvalues
        simp [gepZeroHandles, SemanticAssignment.getValues, hv, hvalues]
      · simp [hlen]
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨it.bitwidth, by rw [hz]⟩
        · exact hzero v hv
      · intro id hid
        rw [heq id (by omega)]
        simp [SemanticAssignment.bindProperty, SemanticAssignment.bindValue, SemanticAssignment.bindType,
          SemanticAssignment.bind, show id ≠ start+3 by omega,
          show id ≠ start+2 by omega, show id ≠ start by omega]

theorem gepZeroDecls_collect (start : Nat) (payloads : List Int) (ctx : HandleContext)
    (hu : ctx.unavailable = []) (hf : gepFreshFrom ctx start) :
    ∃ final, MatchProg.collectDeclBindings (gepZeroDecls start payloads) ctx = some final ∧
      final.unavailable = [] ∧ gepFreshFrom final (start + 4*payloads.length) ∧
      (∀ id, id < start → final.lookup id = ctx.lookup id) ∧
      (∀ handle ∈ gepZeroHandles start payloads, final.require handle = true) := by
  induction payloads generalizing start ctx with
  | nil =>
    refine ⟨ctx,rfl,hu,?_,?_,?_⟩
    · simpa using hf
    · simp
    · simp [gepZeroHandles]
  | cons payload payloads ih =>
    let step : HandleContext :=
      {bindings := (start+1,.op) :: (start+3,.prop (.llvm .mlir__constant)) ::
        (start+2,.value) :: (start,.type) :: ctx.bindings
       unavailable := ctx.unavailable}
    have hs : gepFreshFrom step (start+4) := by
      intro id hid
      simp [step, gep_lookup_prefix, show start+1 ≠ id by omega,
        show start+3 ≠ id by omega, show start+2 ≠ id by omega,
        show start ≠ id by omega, hf id (by omega)]
    obtain ⟨final,hcollect,hu',hf',hold,hvalues⟩ := ih (start+4) step hu hs
    refine ⟨final,?_,hu',?_,?_,?_⟩
    · have ht := hf start (by omega)
      have ho := hf (start+1) (by omega)
      have hv := hf (start+2) (by omega)
      have hp := hf (start+3) (by omega)
      have hctx : (HandleContext.mk ctx.bindings []) = ctx := by cases ctx; simp_all
      simpa [gepZeroDecls, MatchProg.collectDeclBindings, MatchDecl.collectBindings,
        HandleContext.insertManyFresh, HandleContext.insertFresh, HandleContext.requireMany,
        HandleContext.require, gep_lookup_prefix, ht, ho, hv, hp, hu, step, hctx, guard, pure, bind,
        show start ≠ start+1 by omega, show start ≠ start+2 by omega,
        show start ≠ start+3 by omega, show start+2 ≠ start+1 by omega,
        show start+2 ≠ start+3 by omega, show start+3 ≠ start+1 by omega] using hcollect
    · have he : start + 4 * (payload::payloads).length = start+4+4*payloads.length := by simp; omega
      rw [he]
      exact hf'
    · intro id hid
      rw [hold id (by omega)]
      simp [step, gep_lookup_prefix, show start+1 ≠ id by omega,
        show start+3 ≠ id by omega, show start+2 ≠ id by omega, show start ≠ id by omega]
    · intro handle hm
      simp only [gepZeroHandles, Array.mem_append, Array.mem_singleton] at hm
      rcases hm with rfl | hm
      · simp [HandleContext.require, hu', hold (start+2) (by omega), step, gep_lookup_prefix,
          show start+1 ≠ start+2 by omega, show start+3 ≠ start+2 by omega]
      · exact hvalues handle hm

def gepZeroRawGuard (n : Nat) : PropertyMatcher (.llvm .getelementptr : OpCode) :=
  fun props => (props.rawConstantIndices.values.filter (· == -2147483648)).size == n &&
    props.rawConstantIndices.values.all (fun index => index == 0 || index == -2147483648)

/-- All finite dynamic arities and all zero-valued scalar integer literal encodings. -/
def gepAllZeroFamily (payloads : List Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType)
    let p ← MatchProg.value ty
    let indices ← matchGEPZeroIndices payloads
    let _ ← MatchProg.root (.llvm .getelementptr) (#[p] ++ indices) #[ty]
      (gepZeroRawGuard payloads.length)
    return p)
  pure (fun p => p)

def gepAllZeroCore (payloads : List Int) : Pattern OpCode where
  Exports := Handle OpCode .value
  matcher := {
    rootHandle := ⟨2+4*payloads.length⟩
    numHandles := 2+4*payloads.length+3
    exports := ⟨1⟩
    decls := .operation (.llvm .getelementptr) (#[⟨1⟩] ++ gepZeroHandles 2 payloads) #[⟨0⟩]
      (gepZeroRawGuard payloads.length)
      ⟨2+4*payloads.length+2⟩ ⟨2+4*payloads.length⟩ #[⟨2+4*payloads.length+1⟩] rfl ::
      (gepZeroDecls 2 payloads).reverse ++
      [.value ⟨0⟩ ⟨1⟩,
       .type (fun ty => ((ty.cast? LLVM.PointerType).map (fun _ => true)).getD false) ⟨0⟩]
  }
  CreationExports := Handle OpCode .value
  creation := {decls := [], numHandles := 2+4*payloads.length+3, exports := ⟨1⟩}
  replacement := {values := #[⟨1⟩]}

theorem gepAllZeroFamily_eq (payloads : List Int) : gepAllZeroFamily payloads = gepAllZeroCore payloads := by
  unfold gepAllZeroFamily
  unfoldPuddleBuilder
  simp only [matchGEPZeroIndices_run]
  unfoldPuddleBuilder
  simp [gepAllZeroCore, show Array.range 1 = #[0] by decide]

theorem gepZeroDecls_filter_true (start : Nat) (payloads : List Int) (p : MatchDecl OpCode → Bool)
    (ht : ∀ m h, p (.type m h) = true)
    (ho : ∀ c a r m ph oh rs hs, p (.operation c a r m ph oh rs hs) = true) :
    (gepZeroDecls start payloads).filter p = gepZeroDecls start payloads := by
  induction payloads generalizing start with
  | nil => rfl
  | cons payload payloads ih => simp [gepZeroDecls, ht, ho, ih]

theorem gepZeroDecls_filter_false (start : Nat) (payloads : List Int) (p : MatchDecl OpCode → Bool)
    (ht : ∀ m h, p (.type m h) = false)
    (ho : ∀ c a r m ph oh rs hs, p (.operation c a r m ph oh rs hs) = false) :
    (gepZeroDecls start payloads).filter p = [] := by
  induction payloads generalizing start with
  | nil => rfl
  | cons payload payloads ih => simp [gepZeroDecls, ht, ho, ih]

theorem gepAllZeroCore_bindingDecls (payloads : List Int) :
    (gepAllZeroCore payloads).matcher.bindingDecls =
      [.type (fun ty => ((ty.cast? LLVM.PointerType).map (fun _ => true)).getD false) ⟨0⟩,
       .value ⟨0⟩ ⟨1⟩] ++ gepZeroDecls 2 payloads ++
      [.operation (.llvm .getelementptr) (#[⟨1⟩] ++ gepZeroHandles 2 payloads) #[⟨0⟩]
        (gepZeroRawGuard payloads.length)
        ⟨2+4*payloads.length+2⟩ ⟨2+4*payloads.length⟩ #[⟨2+4*payloads.length+1⟩] rfl] := by
  simp only [MatchProg.bindingDecls, gepAllZeroCore, List.partition_eq_filter_filter,
    List.filter_cons, List.filter_append, List.filter_reverse]
  rw [gepZeroDecls_filter_true _ _ _ (by intros; rfl) (by intros; rfl)]
  rw [gepZeroDecls_filter_false _ _ _ (by intros; rfl) (by intros; rfl)]
  simp [List.reverse_append, List.append_assoc]

theorem gepZeroDecls_supported (start : Nat) (payloads : List Int) :
    ∀ d ∈ gepZeroDecls start payloads, d.Supported := by
  induction payloads generalizing start with
  | nil => simp [gepZeroDecls]
  | cons payload payloads ih =>
    intro d hd
    simp only [gepZeroDecls, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · trivial
    · simp [MatchDecl.Supported, SupportedOpCode, get_effects, is_terminator]
    · exact ih (start+4) d hd

theorem gepAllZeroCore_supported (payloads : List Int) : (gepAllZeroCore payloads).Supported := by
  constructor
  · intro d hd
    simp only [gepAllZeroCore, List.mem_cons, List.mem_append, List.mem_reverse,
      List.not_mem_nil, or_false] at hd
    rcases hd with (rfl | hd) | rfl | rfl
    · simp [MatchDecl.Supported, SupportedOpCode, get_effects, is_terminator]
    · exact gepZeroDecls_supported 2 payloads d hd
    · trivial
    · trivial
  · simp [CreateProg.Supported, gepAllZeroCore]

def gepZeroInitialContext : HandleContext := ⟨[(1,.value),(0,.type)],[]⟩

theorem gepAllZeroCore_structure (payloads : List Int) : (gepAllZeroCore payloads).StructurallyWellFormed := by
  have hi : gepFreshFrom gepZeroInitialContext 2 := by
    intro id hid
    simp [gepZeroInitialContext, gep_lookup_prefix, gep_lookup_empty,
      show 1 ≠ id by omega, show 0 ≠ id by omega]
  obtain ⟨ctx,hc,hu,hf,hold,hvalues⟩ := gepZeroDecls_collect 2 payloads gepZeroInitialContext rfl hi
  have h0 : ctx.lookup 0 = some .type := by rw [hold 0 (by omega)]; rfl
  have h1 : ctx.lookup 1 = some .value := by rw [hold 1 (by omega)]; rfl
  have hindices : (gepZeroHandles 2 payloads).toList.all ctx.require = true := by
    apply List.all_eq_true.mpr
    intro handle hm
    exact hvalues handle (by simpa using hm)
  have hoperands : ctx.requireMany ((#[⟨1⟩] : Array (Handle OpCode .value)) ++ gepZeroHandles 2 payloads).toList = true := by
    simp [HandleContext.requireMany, HandleContext.require, hu, h1, hindices]
  have hiLookup : ∀ (i : Nat) (h : i < (gepZeroHandles 2 payloads).size),
      ctx.lookup (gepZeroHandles 2 payloads)[i].id = some .value := by
    intro i h
    have hv := hvalues (gepZeroHandles 2 payloads)[i] (Array.getElem_mem h)
    simpa [HandleContext.require, hu] using hv
  have hr := hf (2+4*payloads.length) (by omega)
  have hv := hf (2+4*payloads.length+1) (by omega)
  have hp := hf (2+4*payloads.length+2) (by omega)
  have hend : (HandleContext.mk ctx.bindings []) = ctx := by cases ctx; simp_all
  simp only [Pattern.StructurallyWellFormed, Pattern.checkStructure, MatchProg.collectBindings,
    gepAllZeroCore_bindingDecls, gep_collectDeclBindings_append]
  simp only [gepAllZeroCore, MatchProg.rootResults?, List.cons_append, ↓reduceIte,
    CreateProg.checkBindings, Replacement.checkBindings, List.foldlM_nil]
  have hprefix : MatchProg.collectDeclBindings
      [.type (fun ty => ((ty.cast? LLVM.PointerType).map (fun _ => true)).getD false) ⟨0⟩,
       .value ⟨0⟩ ⟨1⟩] HandleContext.empty = some gepZeroInitialContext := by rfl
  simp only [hprefix, bind, pure, Option.bind_some]
  rw [hc]
  simp [MatchProg.collectDeclBindings, MatchDecl.collectBindings, HandleContext.insertManyFresh,
    HandleContext.insertFresh, HandleContext.requireMany, HandleContext.require,
    HandleContext.forbidMany, HandleContext.forbid, gep_lookup_prefix, gep_lookup_clear_unavailable,
    hr, hv, hp, hu, h0, h1, hend, hoperands, hiLookup, guard, pure, bind,
    show 2+4*payloads.length+2 ≠ 2+4*payloads.length by omega,
    show 2+4*payloads.length+1 ≠ 2+4*payloads.length by omega,
    show 2+4*payloads.length+1 ≠ 2+4*payloads.length+2 by omega,
    show 2+4*payloads.length+2 ≠ 2+4*payloads.length+1 by omega,
    show 2+4*payloads.length ≠ 1 by omega,
    show 2+4*payloads.length+1 ≠ 1 by omega,
    show 2+4*payloads.length+2 ≠ 1 by omega,
    show 1 ≠ 2+4*payloads.length by omega]

theorem gepAllZeroCore_semantics (payloads : List Int) : (gepAllZeroCore payloads).PreservesSemantics := by
  simp only [Pattern.PreservesSemantics, MatchProg.Models,
    gepAllZeroCore_bindingDecls, gep_modelsDecls_append]
  simpPuddleSemantics
  rintro ⟨⟩
  simp only [RuntimeValue.Conforms.llvmPointerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro p
  apply gepZeroDecls_models
  intro final values hvalues hlen hzero heq
  have h0 : final 0 = some (.type (LLVM.PointerType.mk : TypeAttr)) := by
    rw [heq 0 (by omega)]; rfl
  have hb1 : final 1 = some (.value (.addr p)) := by
    rw [heq 1 (by omega)]; rfl
  have h1 : final.getValue ⟨1⟩ = some (.addr p) := by
    simp [SemanticAssignment.getValue, hb1]
  change List.mapM final.getValue _ = some values at hvalues
  simp only [Array.toList_append, List.cons_append, List.nil_append, List.mapM_cons,
    h1, hvalues, h0, Option.bind_some]
  intro props value hguard hi
  have hg : (props.rawConstantIndices.values.filter (· == -2147483648)).size = payloads.length ∧
      ∀ index ∈ props.rawConstantIndices.values, index = 0 ∨ index = -2147483648 := by
    simpa only [gepZeroRawGuard, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Bool.or_eq_true] using hguard
  have hi' : InterpretsTo (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)]
      (#[.addr p] ++ values.toArray) #[value] := by simpa using hi
  have hr : value ⊒ .addr p := gep_all_zero_refines props values.toArray hg.2
    (by simpa using hzero) (by simpa [hlen] using hg.1) p value hi'
  simp [gepAllZeroCore, CreateProg.modelsDecls, SemanticAssignment.getValue,
    SemanticAssignment.bind, hb1,
    show 2+4*payloads.length+1 ≠ 2+4*payloads.length+2 by omega,
    show 1 ≠ 2+4*payloads.length+1 by omega,
    show 1 ≠ 2+4*payloads.length+2 by omega,
    RuntimeValue.arrayIsRefinedBy_refl, RuntimeValue.arrayIsRefinedBy, hr]

theorem gepAllZeroFamily_valid (payloads : List Int) : Pattern.Valid (gepAllZeroFamily payloads) := by
  rw [gepAllZeroFamily_eq]
  exact ⟨gepAllZeroCore_supported payloads, rfl, gepAllZeroCore_structure payloads,
    gepAllZeroCore_semantics payloads⟩
end Veir.InstSimplify
