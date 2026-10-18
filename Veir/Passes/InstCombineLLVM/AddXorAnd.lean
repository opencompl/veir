module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.AddXorAnd

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

/-- Scalar specialization of InstCombineAddSub.cpp:1802-1806:
    `(A xor B) + (A and B) -> A or B`. -/
public def addXorAnd : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let xor ← MatchProg.operation (.llvm .xor) #[a, b] #[ty] (fun _ => true)
    let and ← MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .add) #[xor.res[0]!, and.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .or) default
    CreateProg.operation (.llvm .or) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem addXorAnd_valid : Pattern.Valid addXorAnd := by
  simp only [addXorAnd]; unfoldPuddleBuilder
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
  rintro ⟨⟩ xor hXor
  obtain rfl := (xor_iff _ _ _ _).mp hXor
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro addProps source hSource
  obtain rfl := (add_iff _ _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.or a b), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (add_xor_and_refines_or w a b addProps.nsw addProps.nuw)

/-- Variant with the matched `and` operands commuted. -/
public def addXorAndCommutedAnd : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let xor ← MatchProg.operation (.llvm .xor) #[a, b] #[ty] (fun _ => true)
    let and ← MatchProg.operation (.llvm .and) #[b, a] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .add) #[xor.res[0]!, and.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .or) default
    CreateProg.operation (.llvm .or) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem addXorAndCommutedAnd_valid : Pattern.Valid addXorAndCommutedAnd := by
  simp only [addXorAndCommutedAnd]; unfoldPuddleBuilder
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
  rintro ⟨⟩ xor hXor
  obtain rfl := (xor_iff _ _ _ _).mp hXor
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro addProps source hSource
  obtain rfl := (add_iff _ _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.or a b), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, llvm_and_comm] using
    (add_xor_and_refines_or w a b addProps.nsw addProps.nuw)

/-- Variant with the root `add` operands commuted. -/
public def addAndXor : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let xor ← MatchProg.operation (.llvm .xor) #[a, b] #[ty] (fun _ => true)
    let and ← MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .add) #[and.res[0]!, xor.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .or) default
    CreateProg.operation (.llvm .or) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem addAndXor_valid : Pattern.Valid addAndXor := by
  simp only [addAndXor]; unfoldPuddleBuilder
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
  rintro ⟨⟩ xor hXor
  obtain rfl := (xor_iff _ _ _ _).mp hXor
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro addProps source hSource
  obtain rfl := (add_iff _ _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.or a b), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (add_and_xor_refines_or w a b addProps.nsw addProps.nuw)

/-- Variant with both the root `add` and inner `and` operands commuted. -/
public def addCommutedAndXor : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let xor ← MatchProg.operation (.llvm .xor) #[a, b] #[ty] (fun _ => true)
    let and ← MatchProg.operation (.llvm .and) #[b, a] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .add) #[and.res[0]!, xor.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .or) default
    CreateProg.operation (.llvm .or) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem addCommutedAndXor_valid : Pattern.Valid addCommutedAndXor := by
  simp only [addCommutedAndXor]; unfoldPuddleBuilder
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
  rintro ⟨⟩ xor hXor
  obtain rfl := (xor_iff _ _ _ _).mp hXor
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro addProps source hSource
  obtain rfl := (add_iff _ _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.or a b), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, llvm_and_comm] using
    (add_and_xor_refines_or w a b addProps.nsw addProps.nuw)

end Veir.Passes.InstCombineLLVM.AddXorAnd
