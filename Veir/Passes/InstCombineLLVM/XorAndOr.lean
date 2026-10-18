module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.XorAndOr

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def xorAndOrPattern (rootCommuted orCommuted : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let and ← MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
      let or ← if orCommuted then
        MatchProg.operation (.llvm .or) #[b, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[a, b] #[ty] (fun _ => true)
      let _ ← if rootCommuted then
        MatchProg.root (.llvm .xor) #[or.res[0]!, and.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[and.res[0]!, or.res[0]!] #[ty] (fun _ => true)
      return (ty, a, b))
    (fun (ty, a, b) => do
      let props ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[a, b] #[ty] props)
    (fun result => result.res[0]!)

private theorem xorAndOrPattern_valid (rootCommuted orCommuted : Bool) :
    Pattern.Valid (xorAndOrPattern rootCommuted orCommuted) := by
  cases rootCommuted <;> cases orCommuted <;>
    simp only [xorAndOrPattern, Bool.false_eq_true, Bool.true_eq_false, if_false, if_true] <;>
    unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
        HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
        HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ a b
    rintro ⟨⟩ and hAnd
    obtain rfl := (and_iff _ _ _ _).mp hAnd
    rintro orProps or hOr
    obtain rfl := (or_iff _ _ _ _ _).mp hOr
    rintro ⟨⟩ source hSource
    obtain rfl := (xor_iff _ _ _ _).mp hSource
    refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self, llvm_or_comm, llvm_xor_comm] using
      (xor_and_or_refines_xor w a b orProps.disjoint)

/-- Scalar specialization of InstCombineAndOrXor.cpp:4830-4832:
    `(A and B) xor (A or B) -> A xor B`. -/
public def xorAndOr : Pattern OpCode := xorAndOrPattern false false

public theorem xorAndOr_valid : Pattern.Valid xorAndOr :=
  xorAndOrPattern_valid false false

/-- Variant with the inner `or` operands commuted. -/
public def xorAndCommutedOr : Pattern OpCode := xorAndOrPattern false true

public theorem xorAndCommutedOr_valid : Pattern.Valid xorAndCommutedOr :=
  xorAndOrPattern_valid false true

/-- Variant with the root `xor` operands commuted. -/
public def xorOrAnd : Pattern OpCode := xorAndOrPattern true false

public theorem xorOrAnd_valid : Pattern.Valid xorOrAnd :=
  xorAndOrPattern_valid true false

/-- Variant with root `xor` and inner `and` commutation from the source matcher. -/
public def xorOrCommutedAnd : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let and ← MatchProg.operation (.llvm .and) #[b, a] #[ty] (fun _ => true)
      let or ← MatchProg.operation (.llvm .or) #[a, b] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .xor) #[or.res[0]!, and.res[0]!] #[ty] (fun _ => true)
      return (ty, a, b))
    (fun (ty, a, b) => do
      let props ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[a, b] #[ty] props)
    (fun result => result.res[0]!)

public theorem xorOrCommutedAnd_valid : Pattern.Valid xorOrCommutedAnd := by
  simp only [xorOrCommutedAnd]; unfoldPuddleBuilder
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
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro orProps or hOr
  obtain rfl := (or_iff _ _ _ _ _).mp hOr
  rintro ⟨⟩ source hSource
  obtain rfl := (xor_iff _ _ _ _).mp hSource
  refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, llvm_and_comm, llvm_xor_comm] using
    (xor_and_or_refines_xor w a b orProps.disjoint)

end Veir.Passes.InstCombineLLVM.XorAndOr
