module
public import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.SubCompareSub
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl
private def pattern (pred : LLVM.IntPred) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType); let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth=1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty; let c ← MatchProg.value ty
    let l ← MatchProg.operation (.llvm .sub) #[a,b] #[ty] (fun _ => true)
    let r ← MatchProg.operation (.llvm .sub) #[c,b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .icmp) #[l.res[0]!,r.res[0]!] #[bt] (fun p => p.predicate=pred)
    return (bt,a,c))
  (fun (bt,a,c) => do
    let cp ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk pred)
    CreateProg.operation (.llvm .icmp) #[a,c] #[bt] cp)
  (fun r => r.res[0]!)
private theorem valid (pred : LLVM.IntPred) (hp : pred=.eq ∨ pred=.ne) : Pattern.Valid (pattern pred) := by
  rcases hp with rfl | rfl <;> simp only [pattern] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ bt ⟨bw,bs⟩ hbt hbw; subst bt; change bw=1 at hbw; subst bw
    rintro a b c lp lv hl; obtain rfl := (sub_iff _ _ _ _ _).mp hl
    rintro rp rv hr; obtain rfl := (sub_iff _ _ _ _ _).mp hr
    rintro cp cv hm hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc; rw [hm]
  · refine ⟨.int 1 (LLVM.Int.icmp a c .eq), (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    simpa only [LLVM.Int.cast_self] using icmp_sub_sub_eq_flags a b c lp.nsw lp.nuw rp.nsw rp.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp a c .ne), (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    simpa only [LLVM.Int.cast_self] using icmp_sub_sub_ne_flags a b c lp.nsw lp.nuw rp.nsw rp.nuw
public def subCompareSubEq : Pattern OpCode := pattern .eq
public theorem subCompareSubEq_valid : Pattern.Valid subCompareSubEq := valid .eq (Or.inl rfl)
public def subCompareSubNe : Pattern OpCode := pattern .ne
public theorem subCompareSubNe_valid : Pattern.Valid subCompareSubNe := valid .ne (Or.inr rfl)

private def relationalPattern : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let c ← MatchProg.value ty
    let l ← MatchProg.operation (.llvm .sub) #[a, b] #[ty] (fun _ => true)
    let r ← MatchProg.operation (.llvm .sub) #[c, b] #[ty] (fun _ => true)
    let root ← MatchProg.root (.llvm .icmp) #[l.res[0]!, r.res[0]!] #[bt]
    MatchProg.matchNative (root.properties, l.properties, r.properties) fun (cp, lp, rp) =>
      compareCancellationAllowed cp.predicate lp.nsw lp.nuw &&
        compareCancellationAllowed cp.predicate rp.nsw rp.nuw
    return (bt, a, c, root))
  (fun (bt, a, c, root) =>
    CreateProg.operation (.llvm .icmp) #[a, c] #[bt] root.properties)
  (fun r => r.res[0]!)

private theorem relationalPattern_valid : Pattern.Valid relationalPattern := by
  simp only [relationalPattern]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, MatchProg.collectBindings,
      MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
      HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
      HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
      HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
      MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
      CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ bt ⟨bw, bs⟩ hbt hbw; subst bt; change bw = 1 at hbw; subst bw
  rintro a b c lp lv hl; obtain rfl := (sub_iff _ _ _ _ _).mp hl
  rintro rp rv hr; obtain rfl := (sub_iff _ _ _ _ _).mp hr
  rintro cp cv hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc
  rintro hlallowed hrallowed
  let lp' : NswNuwProperties := lp
  let rp' : NswNuwProperties := rp
  let cp' : IcmpProperties := cp
  change compareCancellationAllowed cp'.predicate lp'.nsw lp'.nuw = true at hlallowed
  change compareCancellationAllowed cp'.predicate rp'.nsw rp'.nuw = true at hrallowed
  refine ⟨.int 1 (LLVM.Int.icmp a c cp'.predicate),
    (icmp_iff _ cp _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
  simpa only [LLVM.Int.cast_self] using
    icmp_sub_sub_pred_flags cp'.predicate a b c lp'.nsw lp'.nuw rp'.nsw rp'.nuw
      hlallowed hrallowed

public def subCompareSubRelational : Pattern OpCode := relationalPattern
public theorem subCompareSubRelational_valid : Pattern.Valid subCompareSubRelational :=
  relationalPattern_valid
end Veir.Passes.InstCombineLLVM.SubCompareSub
