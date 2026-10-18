module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SubOrAnd

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

/-- Scalar specialization of InstCombineAddSub.cpp:2727-2733:
    `(A or B) - (A and B) -> A xor B`. -/
public def subOrAnd : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let or ← MatchProg.operation (.llvm .or) #[a, b] #[ty] (fun _ => true)
    let and ← MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[or.res[0]!, and.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .xor) ()
    CreateProg.operation (.llvm .xor) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem subOrAnd_valid : Pattern.Valid subOrAnd := by
  simp only [subOrAnd]; unfoldPuddleBuilder
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
  rintro orProps or hOr
  obtain rfl := (or_iff _ _ _ _ _).mp hOr
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (sub_or_and_refines_xor w a b orProps.disjoint subProps.nsw subProps.nuw)

/-- Variant with the matched `or` operands commuted. -/
public def subCommutedOrAnd : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let or ← MatchProg.operation (.llvm .or) #[b, a] #[ty] (fun _ => true)
    let and ← MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[or.res[0]!, and.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .xor) ()
    CreateProg.operation (.llvm .xor) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem subCommutedOrAnd_valid : Pattern.Valid subCommutedOrAnd := by
  simp only [subCommutedOrAnd]; unfoldPuddleBuilder
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
  rintro orProps or hOr
  obtain rfl := (or_iff _ _ _ _ _).mp hOr
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, llvm_or_comm] using
    (sub_or_and_refines_xor w a b orProps.disjoint subProps.nsw subProps.nuw)

end Veir.Passes.InstCombineLLVM.SubOrAnd
