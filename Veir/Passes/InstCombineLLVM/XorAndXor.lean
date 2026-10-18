module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.XorAndXor

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def xorAndXorPattern (rootCommuted innerCommuted : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let and ← if rootCommuted && innerCommuted then
        MatchProg.operation (.llvm .and) #[b, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
      let xor ← if !rootCommuted && innerCommuted then
        MatchProg.operation (.llvm .xor) #[b, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[a, b] #[ty] (fun _ => true)
      let _ ← if rootCommuted then
        MatchProg.root (.llvm .xor) #[xor.res[0]!, and.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[and.res[0]!, xor.res[0]!] #[ty] (fun _ => true)
      return (ty, a, b))
    (fun (ty, a, b) => do
      let props ← CreateProg.property (.llvm .or) default
      CreateProg.operation (.llvm .or) #[a, b] #[ty] props)
    (fun result => result.res[0]!)

private theorem xorAndXorPattern_valid (rootCommuted innerCommuted : Bool) :
    Pattern.Valid (xorAndXorPattern rootCommuted innerCommuted) := by
  cases rootCommuted <;> cases innerCommuted <;>
    simp only [xorAndXorPattern, Bool.false_and, Bool.true_and, Bool.not_false,
      Bool.not_true, Bool.true_eq, Bool.false_eq_true, ite_false, ite_true] <;>
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
    rintro ⟨⟩ xor hXor
    obtain rfl := (xor_iff _ _ _ _).mp hXor
    rintro ⟨⟩ source hSource
    obtain rfl := (xor_iff _ _ _ _).mp hSource
    refine ⟨.int w (LLVM.Int.or a b), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self, llvm_and_comm, llvm_xor_comm] using
      (xor_and_xor_refines_or w a b)

/-- Scalar specialization of InstCombineAndOrXor.cpp:5714-5716:
    `(A and B) xor (A xor B) -> A or B`. -/
public def xorAndXor : Pattern OpCode := xorAndXorPattern false false

public theorem xorAndXor_valid : Pattern.Valid xorAndXor :=
  xorAndXorPattern_valid false false

/-- Variant with the inner `xor` operands commuted. -/
public def xorAndCommutedXor : Pattern OpCode := xorAndXorPattern false true

public theorem xorAndCommutedXor_valid : Pattern.Valid xorAndCommutedXor :=
  xorAndXorPattern_valid false true

/-- Variant with the root terms commuted. -/
public def xorXorAnd : Pattern OpCode := xorAndXorPattern true false

public theorem xorXorAnd_valid : Pattern.Valid xorXorAnd :=
  xorAndXorPattern_valid true false

/-- Variant with the root terms and inner `and` operands commuted. -/
public def xorXorCommutedAnd : Pattern OpCode := xorAndXorPattern true true

public theorem xorXorCommutedAnd_valid : Pattern.Valid xorXorCommutedAnd :=
  xorAndXorPattern_valid true true

end Veir.Passes.InstCombineLLVM.XorAndXor
