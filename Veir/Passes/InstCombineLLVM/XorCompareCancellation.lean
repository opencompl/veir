module
public import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.XorCompareCancellation
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl
/-- Arbitrary-width scalar equality specialization of InstCombineCompares.cpp:6289-6290. -/
public def xorCompareCancellation : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth=1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty; let d ← MatchProg.value ty
    let l ← MatchProg.operation (.llvm .xor) #[a,b] #[ty] (fun _ => true)
    let r ← MatchProg.operation (.llvm .xor) #[a,d] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .icmp) #[l.res[0]!,r.res[0]!] #[bt]
      (fun p => p.predicate=.eq)
    return (bt,b,d))
  (fun (bt,b,d) => do
    let p ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .eq)
    CreateProg.operation (.llvm .icmp) #[b,d] #[bt] p)
  (fun r => r.res[0]!)
public theorem xorCompareCancellation_valid : Pattern.Valid xorCompareCancellation := by
  simp only [xorCompareCancellation]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩
  rintro bt ⟨bw,bs⟩ hbt hbw; subst bt; change bw=1 at hbw; subst bw
  rintro a b d
  rintro ⟨⟩ lv hl; obtain rfl := (xor_iff _ _ _ _).mp hl
  rintro ⟨⟩ rv hr; obtain rfl := (xor_iff _ _ _ _).mp hr
  rintro cp cv hp hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc; rw [hp]
  refine ⟨.int 1 (LLVM.Int.icmp b d .eq),
    (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
  simpa only [LLVM.Int.cast_self] using icmp_xor_xor_eq a b d

/-- NE-predicate variant from the same LLVM source branch. -/
public def xorCompareCancellationNe : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth=1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty; let d ← MatchProg.value ty
    let l ← MatchProg.operation (.llvm .xor) #[a,b] #[ty] (fun _ => true)
    let r ← MatchProg.operation (.llvm .xor) #[a,d] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .icmp) #[l.res[0]!,r.res[0]!] #[bt]
      (fun p => p.predicate=.ne)
    return (bt,b,d))
  (fun (bt,b,d) => do
    let p ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .ne)
    CreateProg.operation (.llvm .icmp) #[b,d] #[bt] p)
  (fun r => r.res[0]!)
public theorem xorCompareCancellationNe_valid : Pattern.Valid xorCompareCancellationNe := by
  simp only [xorCompareCancellationNe]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩
  rintro bt ⟨bw,bs⟩ hbt hbw; subst bt; change bw=1 at hbw; subst bw
  rintro a b d
  rintro ⟨⟩ lv hl; obtain rfl := (xor_iff _ _ _ _).mp hl
  rintro ⟨⟩ rv hr; obtain rfl := (xor_iff _ _ _ _).mp hr
  rintro cp cv hp hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc; rw [hp]
  refine ⟨.int 1 (LLVM.Int.icmp b d .ne),
    (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
  simpa only [LLVM.Int.cast_self] using icmp_xor_xor_ne a b d

end Veir.Passes.InstCombineLLVM.XorCompareCancellation
