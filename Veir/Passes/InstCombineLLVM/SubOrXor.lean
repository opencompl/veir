module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SubOrXor

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

/-- Scalar specialization of InstCombineAddSub.cpp:2760-2766:
    `(A or B) - (A xor B) -> A and B`. -/
public def subOrXor : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let or ← MatchProg.operation (.llvm .or) #[a, b] #[ty] (fun _ => true)
    let xor ← MatchProg.operation (.llvm .xor) #[a, b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[or.res[0]!, xor.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .and) ()
    CreateProg.operation (.llvm .and) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem subOrXor_valid : Pattern.Valid subOrXor := by
  simp only [subOrXor]; unfoldPuddleBuilder
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
  rintro ⟨⟩ xor hXor
  obtain rfl := (xor_iff _ _ _ _).mp hXor
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.and a b), (and_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (sub_or_xor_refines_and w a b orProps.disjoint subProps.nsw subProps.nuw)

/-- Variant with the matched `or` operands commuted. -/
public def subCommutedOrXor : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let or ← MatchProg.operation (.llvm .or) #[b, a] #[ty] (fun _ => true)
    let xor ← MatchProg.operation (.llvm .xor) #[a, b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[or.res[0]!, xor.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .and) ()
    CreateProg.operation (.llvm .and) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem subCommutedOrXor_valid : Pattern.Valid subCommutedOrXor := by
  simp only [subCommutedOrXor]; unfoldPuddleBuilder
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
  rintro ⟨⟩ xor hXor
  obtain rfl := (xor_iff _ _ _ _).mp hXor
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.and a b), (and_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, llvm_or_comm] using
    (sub_or_xor_refines_and w a b orProps.disjoint subProps.nsw subProps.nuw)

end Veir.Passes.InstCombineLLVM.SubOrXor
