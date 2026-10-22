import Veir.InstSimplify.GEPDynamicSchema
import Veir.InstSimplify.GEPPoisonIndexSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

private def gepPoisonPrefix : List (MatchDecl OpCode) :=
  [.type (fun ty => ((ty.cast? LLVM.PointerType).map (fun _ => true)).getD false) ⟨0⟩,
   .value ⟨0⟩ ⟨1⟩,
   .type (fun ty => ((ty.cast? IntegerType).map (fun _ => true)).getD false) ⟨2⟩,
   .operation (.llvm .mlir__poison) #[] #[⟨2⟩] (fun _ => true) ⟨5⟩ ⟨3⟩ #[⟨4⟩] rfl]

private def gepPoisonOperands (before after : Nat) : Array (Handle OpCode .value) :=
  #[⟨1⟩] ++ gepDynamicHandles 6 before ++ #[⟨4⟩] ++ gepDynamicHandles (6+2*before) after

private def gepPoisonBindings (before after : Nat) : List (MatchDecl OpCode) :=
  gepPoisonPrefix ++ gepDynamicDecls 6 before ++ gepDynamicDecls (6+2*before) after ++
    [.operation (.llvm .getelementptr) (gepPoisonOperands before after) #[⟨0⟩]
      (gepDynamicRawCount (before+1+after))
      ⟨6+2*before+2*after+2⟩ ⟨6+2*before+2*after⟩ #[⟨6+2*before+2*after+1⟩] rfl]

/-- A poison dynamic index with arbitrary numbers of scalar indices on either side.
The raw metadata may interleave arbitrary static indices with these dynamic operands. -/
def gepPoisonIndexFamily (before after : Nat) : Pattern OpCode where
  Exports := Handle OpCode .type
  matcher := {
    rootHandle := ⟨6+2*before+2*after⟩
    numHandles := 6+2*before+2*after+3
    exports := ⟨0⟩
    decls := (gepPoisonBindings before after).reverse
  }
  CreationExports := Handle OpCode .value
  creation := {
    decls := [.property (.llvm .mlir__poison) () ⟨6+2*before+2*after+3⟩,
      .operation (.llvm .mlir__poison) #[] #[⟨0⟩] ⟨6+2*before+2*after+3⟩
        ⟨6+2*before+2*after+4⟩ #[⟨6+2*before+2*after+5⟩]]
    numHandles := 6+2*before+2*after+6
    exports := ⟨6+2*before+2*after+5⟩
  }
  replacement := { values := #[⟨6+2*before+2*after+5⟩] }

private theorem gepPoisonBindings_filters (before after : Nat) :
    (gepPoisonBindings before after).filter gepStructuralDecl = gepPoisonBindings before after ∧
    (gepPoisonBindings before after).filter (fun d => !gepStructuralDecl d) = [] := by
  simp [gepPoisonBindings,gepPoisonPrefix,gepStructuralDecl,List.filter_append,
    (gepDynamicDecls_filter 6 before).1,(gepDynamicDecls_filter 6 before).2,
    (gepDynamicDecls_filter (6+2*before) after).1,(gepDynamicDecls_filter (6+2*before) after).2]

private theorem gepPoisonIndex_bindingDecls (before after : Nat) :
    (gepPoisonIndexFamily before after).matcher.bindingDecls = gepPoisonBindings before after := by
  simp only [MatchProg.bindingDecls, gepPoisonIndexFamily,List.partition_eq_filter_filter,
    List.filter_reverse]
  simp only [gepPoisonBindings,gepPoisonPrefix,List.filter_append,List.filter_cons,List.filter_nil]
  rw [gepDynamicDecls_filter_true _ _ _ (by intros; rfl) (by intros; rfl)]
  rw [gepDynamicDecls_filter_true _ _ _ (by intros; rfl) (by intros; rfl)]
  rw [gepDynamicDecls_filter_false _ _ _ (by intros; rfl) (by intros; rfl)]
  rw [gepDynamicDecls_filter_false _ _ _ (by intros; rfl) (by intros; rfl)]
  simp

private theorem gepPoisonIndex_supported (before after : Nat) :
    (gepPoisonIndexFamily before after).Supported := by
  constructor
  · intro d hd
    simp only [gepPoisonIndexFamily,List.mem_reverse,gepPoisonBindings,List.mem_append,
      gepPoisonPrefix,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with (((rfl | rfl | rfl | rfl) | hd) | hd) | rfl
    · trivial
    · trivial
    · trivial
    · simp [MatchDecl.Supported,SupportedOpCode,get_effects,is_terminator]
    · exact gepDynamicDecls_supported 6 before d hd
    · exact gepDynamicDecls_supported (6+2*before) after d hd
    · simp [MatchDecl.Supported,SupportedOpCode,get_effects,is_terminator]
  · simp [CreateProg.Supported,gepPoisonIndexFamily,CreateDecl.Supported,SupportedOpCode,get_effects,is_terminator]

private def gepPoisonInitialContext : HandleContext :=
  ⟨[(3,.op),(5,.prop (.llvm .mlir__poison)),(4,.value),(2,.type),(1,.value),(0,.type)],[]⟩

private theorem gepPoisonIndex_structure (before after : Nat) :
    (gepPoisonIndexFamily before after).StructurallyWellFormed := by
  have hi : gepFreshFrom gepPoisonInitialContext 6 := by
    intro id hid
    simp [gepPoisonInitialContext,gep_lookup_prefix,gep_lookup_empty,
      show 3 ≠ id by omega,show 5 ≠ id by omega,show 4 ≠ id by omega,
      show 2 ≠ id by omega,show 1 ≠ id by omega,show 0 ≠ id by omega]
  obtain ⟨middle,hfirst,hum,hfm,holdm,hfront⟩ :=
    gepDynamicDecls_collect 6 before gepPoisonInitialContext rfl hi
  obtain ⟨ctx,hsecond,hu,hf,hold,hback⟩ :=
    gepDynamicDecls_collect (6+2*before) after middle hum hfm
  have h0 : ctx.lookup 0 = some .type := by
    rw [hold 0 (by omega),holdm 0 (by omega)]; rfl
  have h1 : ctx.lookup 1 = some .value := by
    rw [hold 1 (by omega),holdm 1 (by omega)]; rfl
  have h4 : ctx.lookup 4 = some .value := by
    rw [hold 4 (by omega),holdm 4 (by omega)]; rfl
  have hfrontLookup : ∀ handle ∈ gepDynamicHandles 6 before,
      ctx.lookup handle.id = some .value := by
    intro handle hm
    have hb := gepDynamicHandles_bounds 6 before handle hm
    rw [hold handle.id hb.2]
    have h := hfront handle hm
    simpa [HandleContext.require,hum] using h
  have hbackLookup : ∀ handle ∈ gepDynamicHandles (6+2*before) after,
      ctx.lookup handle.id = some .value := by
    intro handle hm
    have h := hback handle hm
    simpa [HandleContext.require,hu] using h
  have hopLookup : ∀ handle ∈ gepPoisonOperands before after,
      ctx.lookup handle.id = some .value := by
    intro handle hm
    simp only [gepPoisonOperands,Array.mem_append,Array.mem_singleton] at hm
    rcases hm with ((rfl | hm) | rfl) | hm
    · exact h1
    · exact hfrontLookup handle hm
    · exact h4
    · exact hbackLookup handle hm
  have hoperands : ctx.requireMany (gepPoisonOperands before after).toList = true := by
    apply List.all_eq_true.mpr
    intro handle hm
    simp [HandleContext.require,hu,hopLookup handle (by simpa using hm)]
  have hiLookup : ∀ (i : Nat) (h : i < (gepPoisonOperands before after).size),
      ctx.lookup (gepPoisonOperands before after)[i].id = some .value := by
    intro i h
    exact hopLookup _ (Array.getElem_mem h)
  have hr := hf (6+2*before+2*after) (by omega)
  have hv := hf (6+2*before+2*after+1) (by omega)
  have hp := hf (6+2*before+2*after+2) (by omega)
  have hcp := hf (6+2*before+2*after+3) (by omega)
  have hco := hf (6+2*before+2*after+4) (by omega)
  have hcv := hf (6+2*before+2*after+5) (by omega)
  have hend : HandleContext.mk ctx.bindings [] = ctx := by cases ctx; simp_all
  have hprefix : MatchProg.collectDeclBindings gepPoisonPrefix HandleContext.empty =
      some gepPoisonInitialContext := by rfl
  simp only [Pattern.StructurallyWellFormed,Pattern.checkStructure,MatchProg.collectBindings,
    gepPoisonIndex_bindingDecls,gepPoisonBindings,gep_collectDeclBindings_append]
  simp only [hprefix,Option.bind_some]
  rw [hfirst]
  simp only [Option.bind_some]
  rw [hsecond]
  simp only [Option.bind_some]
  simp [gepPoisonIndexFamily,gepPoisonBindings,gepPoisonPrefix,List.reverse_append,
    MatchProg.rootResults?,MatchProg.collectDeclBindings,MatchDecl.collectBindings,
    CreateProg.checkBindings,CreateDecl.checkBindings,Replacement.checkBindings,
    HandleContext.insertManyFresh,HandleContext.insertFresh,HandleContext.requireMany,
    HandleContext.require,HandleContext.forbidMany,HandleContext.forbid,
    gep_lookup_prefix,gep_lookup_clear_unavailable,hr,hv,hp,hcp,hco,hcv,hu,h0,h1,h4,hend,
    hoperands,hiLookup,guard,pure,bind]
  simp [show (0:Nat) ≠ 6+2*before+2*after by omega,
    bind,pure,gep_lookup_prefix]

private theorem gepPoisonMapM_congr {α β : Type} (f g : α → Option β) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,h x (by simp),ih (by intro a ha; exact h a (by simp [ha]))]

private theorem gepPoisonMapM_length {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simpa using h.symm
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons,hx] at h
    | some y =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons,hx,ht] at h
      | some tail =>
        simp [List.mapM_cons,hx,ht] at h
        subst ys
        simpa using congrArg Nat.succ (ih tail ht)

private theorem gepPoisonHandles_size (start n : Nat) : (gepDynamicHandles start n).size = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [gepDynamicHandles,ih,Nat.add_comm]

private theorem gepPoisonIndex_semantics (before after : Nat) :
    (gepPoisonIndexFamily before after).PreservesSemantics := by
  simp only [Pattern.PreservesSemantics,MatchProg.Models,gepPoisonIndex_bindingDecls,
    gepPoisonBindings,gep_modelsDecls_append,gepPoisonPrefix]
  simpPuddleSemantics
  rintro ⟨⟩ base hbase ⟨width,signKind⟩ props poison hp
  obtain rfl := (poison_iff ⟨width,signKind⟩ props poison).mp hp
  obtain ⟨p,rfl⟩ := RuntimeValue.Conforms.llvmPointerType.mp hbase
  apply gepDynamicDecls_models
  intro middle front hfront hmiddle
  apply gepDynamicDecls_models
  intro final back hback hfinal
  have hfsize : front.length = before := by
    have h := gepPoisonMapM_length middle.getValue _ front hfront
    simpa [gepPoisonHandles_size] using h
  have hbsize : back.length = after := by
    have h := gepPoisonMapM_length final.getValue _ back hback
    simpa [gepPoisonHandles_size] using h
  have hfront' : final.getValues (gepDynamicHandles 6 before).toList = some front := by
    unfold SemanticAssignment.getValues at *
    have hh : ∀ handle ∈ (gepDynamicHandles 6 before).toList,
        final.getValue handle = middle.getValue handle := by
      intro handle hm
      have hb := gepDynamicHandles_bounds 6 before handle (by simpa using hm)
      simp [SemanticAssignment.getValue,hfinal handle.id hb.2]
    rw [gepPoisonMapM_congr _ _ _ hh]
    exact hfront
  have h0 : final 0 = some (.type (LLVM.PointerType.mk : TypeAttr)) := by
    rw [hfinal 0 (by omega),hmiddle 0 (by omega)]
    rfl
  have h1 : final.getValue ⟨1⟩ = some (.addr p) := by
    unfold SemanticAssignment.getValue
    rw [hfinal 1 (by omega),hmiddle 1 (by omega)]
    rfl
  have h4 : final.getValue ⟨4⟩ = some (.int width .poison) := by
    unfold SemanticAssignment.getValue
    rw [hfinal 4 (by omega),hmiddle 4 (by omega)]
    rfl
  change List.mapM final.getValue _ = some front at hfront'
  change List.mapM final.getValue _ = some back at hback
  simp only [gepPoisonOperands,SemanticAssignment.getValues,Array.toList_append,List.mapM_append,
    List.mapM_cons,List.mapM_nil,Option.bind_some,h1,h4,h0]
  rw [hfront',hback]
  simp only [Option.bind_some,Option.pure_def,List.nil_append,List.append_nil]
  intro gp value hcount hi
  have hi' : InterpretsTo (.llvm .getelementptr) gp #[(LLVM.PointerType.mk : TypeAttr)]
      (#[.addr p] ++ (front ++ [RuntimeValue.int width .poison] ++ back).toArray) #[value] := by simpa using hi
  have hc : (gp.rawConstantIndices.values.filter (· == -2147483648)).size =
      (front ++ [RuntimeValue.int width .poison] ++ back).toArray.size := by
    simp only [gepDynamicRawCount,beq_iff_eq] at hcount
    simpa [hfsize,hbsize,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hcount
  obtain rfl := gep_poison_index_refines gp _ hc ⟨width,by simp⟩ p value hi'
  simp [gepPoisonIndexFamily,gepPoisonBindings,gepPoisonPrefix,List.reverse_append,
    CreateProg.modelsDecls,CreateDecl.Models,SemanticAssignment.getValue,SemanticAssignment.getType,
    SemanticAssignment.getProperty,SemanticAssignment.bind,MatchProg.rootResults?]
  simp [SemanticAssignment.bindProperty,SemanticAssignment.bindValue,
    SemanticAssignment.getValues,SemanticAssignment.getTypes,SemanticAssignment.getType,
    SemanticAssignment.bind,SemanticAssignment.ExistsValues,h0,
    show (0:Nat) ≠ 6+2*before+2*after+1 by omega,
    show (0:Nat) ≠ 6+2*before+2*after+2 by omega,
    show (0:Nat) ≠ 6+2*before+2*after+3 by omega]
  exact ⟨.addr .poison,(ptr_poison_iff () (.addr .poison)).mpr rfl,
    by simp [RuntimeValue.isRefinedBy,isRefinedBy]⟩

/-- Every finite index position and arity is covered by choosing the counts on either side. -/
theorem gepPoisonIndexFamily_valid (before after : Nat) :
    Pattern.Valid (gepPoisonIndexFamily before after) := by
  exact ⟨gepPoisonIndex_supported before after,by
      simp [MatchProg.ConstrainsRoot,MatchProg.rootResults?,gepPoisonIndexFamily,
        gepPoisonBindings,gepPoisonPrefix,List.reverse_append],gepPoisonIndex_structure before after,
    gepPoisonIndex_semantics before after⟩

end Veir.InstSimplify
