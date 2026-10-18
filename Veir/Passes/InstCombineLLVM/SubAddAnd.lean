module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SubAddAnd

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

/-- Scalar specialization of InstCombineAddSub.cpp:2743-2749:
    `(A + B) - (A and B) -> A or B`. -/
public def subAddAnd : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let add ← MatchProg.operation (.llvm .add) #[a, b] #[ty] (fun _ => true)
    let and ← MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[add.res[0]!, and.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .or) default
    CreateProg.operation (.llvm .or) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem subAddAnd_valid : Pattern.Valid subAddAnd := by
  simp only [subAddAnd]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ a b
  rintro addProps add hAdd
  obtain rfl := (add_iff _ _ _ _ _).mp hAdd
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.or a b), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (sub_add_and_refines_or w a b addProps.nsw addProps.nuw subProps.nsw subProps.nuw)

/-- Variant with the matched `and` operands commuted. -/
public def subAddCommutedAnd : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let add ← MatchProg.operation (.llvm .add) #[a, b] #[ty] (fun _ => true)
    let and ← MatchProg.operation (.llvm .and) #[b, a] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[add.res[0]!, and.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .or) default
    CreateProg.operation (.llvm .or) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem subAddCommutedAnd_valid : Pattern.Valid subAddCommutedAnd := by
  simp only [subAddCommutedAnd]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ a b
  rintro addProps add hAdd
  obtain rfl := (add_iff _ _ _ _ _).mp hAdd
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.or a b), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, llvm_and_comm] using
    (sub_add_and_refines_or w a b addProps.nsw addProps.nuw subProps.nsw subProps.nuw)

end Veir.Passes.InstCombineLLVM.SubAddAnd
