module
public import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.OrUgtToNe
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl
/-- Arbitrary-width, non-disjoint scalar specialization of InstCombineCompares.cpp:5265-5269. -/
public def orUgtToNe : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let x ← MatchProg.value ty; let y ← MatchProg.value ty
    let o ← MatchProg.operation (.llvm .or) #[x,y] #[ty] (fun p => p.disjoint = false)
    let _ ← MatchProg.root (.llvm .icmp) #[o.res[0]!,x] #[bt] (fun p => p.predicate = .ugt)
    return (bt,o.res[0]!,x))
  (fun (bt,l,r) => do
    let p ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .ne)
    CreateProg.operation (.llvm .icmp) #[l,r] #[bt] p)
  (fun r => r.res[0]!)
public theorem orUgtToNe_valid : Pattern.Valid orUgtToNe := by
  simp only [orUgtToNe]; unfoldPuddleBuilder
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
  rintro x y
  rintro op ov hd ho
  obtain rfl := (or_iff _ op _ _ _).mp ho
  rw [hd]
  rintro cp cv hp hc
  obtain rfl := (icmp_iff _ cp _ _ _).mp hc
  rw [hp]
  refine ⟨.int 1 (LLVM.Int.icmp (LLVM.Int.or x y false) x .ne),
    (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
  simpa only [LLVM.Int.cast_self, icmp_or_ugt_ne] using
    (isRefinedBy_refl (LLVM.Int.icmp (LLVM.Int.or x y false) x .ne))

/-- Symmetric compare orientation accepted by the same LLVM source branch. -/
public def orUgtToNeSwapped : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let x ← MatchProg.value ty; let y ← MatchProg.value ty
    let o ← MatchProg.operation (.llvm .or) #[x,y] #[ty] (fun p => p.disjoint = false)
    let _ ← MatchProg.root (.llvm .icmp) #[x,o.res[0]!] #[bt] (fun p => p.predicate = .ult)
    return (bt,x,o.res[0]!))
  (fun (bt,l,r) => do
    let p ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .ne)
    CreateProg.operation (.llvm .icmp) #[l,r] #[bt] p)
  (fun r => r.res[0]!)
public theorem orUgtToNeSwapped_valid : Pattern.Valid orUgtToNeSwapped := by
  simp only [orUgtToNeSwapped]; unfoldPuddleBuilder
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
  rintro x y
  rintro op ov hd ho
  obtain rfl := (or_iff _ op _ _ _).mp ho
  rw [hd]
  rintro cp cv hp hc
  obtain rfl := (icmp_iff _ cp _ _ _).mp hc
  rw [hp]
  refine ⟨.int 1 (LLVM.Int.icmp x (LLVM.Int.or x y false) .ne),
    (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
  simpa only [LLVM.Int.cast_self, icmp_or_ult_ne_swapped] using
    (isRefinedBy_refl (LLVM.Int.icmp x (LLVM.Int.or x y false) .ne))


/-- Disjoint-flag specialization of the same source shape. -/
public def orUgtToNeDisjoint : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let x ← MatchProg.value ty; let y ← MatchProg.value ty
    let o ← MatchProg.operation (.llvm .or) #[x,y] #[ty] (fun p => p.disjoint = true)
    let _ ← MatchProg.root (.llvm .icmp) #[o.res[0]!,x] #[bt] (fun p => p.predicate = .ugt)
    return (bt,o.res[0]!,x))
  (fun (bt,l,r) => do
    let p ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .ne)
    CreateProg.operation (.llvm .icmp) #[l,r] #[bt] p)
  (fun r => r.res[0]!)
public theorem orUgtToNeDisjoint_valid : Pattern.Valid orUgtToNeDisjoint := by
  simp only [orUgtToNeDisjoint]; unfoldPuddleBuilder
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
  rintro x y
  rintro op ov hd ho
  obtain rfl := (or_iff _ op _ _ _).mp ho
  rw [hd]
  rintro cp cv hp hc
  obtain rfl := (icmp_iff _ cp _ _ _).mp hc
  rw [hp]
  refine ⟨.int 1 (LLVM.Int.icmp (LLVM.Int.or x y true) x .ne),
    (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
  simpa only [LLVM.Int.cast_self, icmp_or_ugt_ne_disjoint] using
    (isRefinedBy_refl (LLVM.Int.icmp (LLVM.Int.or x y true) x .ne))


/-- Disjoint-flag specialization of the same source shape. -/
public def orUgtToNeSwappedDisjoint : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let x ← MatchProg.value ty; let y ← MatchProg.value ty
    let o ← MatchProg.operation (.llvm .or) #[x,y] #[ty] (fun p => p.disjoint = true)
    let _ ← MatchProg.root (.llvm .icmp) #[x,o.res[0]!] #[bt] (fun p => p.predicate = .ult)
    return (bt,x,o.res[0]!))
  (fun (bt,l,r) => do
    let p ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .ne)
    CreateProg.operation (.llvm .icmp) #[l,r] #[bt] p)
  (fun r => r.res[0]!)
public theorem orUgtToNeSwappedDisjoint_valid : Pattern.Valid orUgtToNeSwappedDisjoint := by
  simp only [orUgtToNeSwappedDisjoint]; unfoldPuddleBuilder
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
  rintro x y
  rintro op ov hd ho
  obtain rfl := (or_iff _ op _ _ _).mp ho
  rw [hd]
  rintro cp cv hp hc
  obtain rfl := (icmp_iff _ cp _ _ _).mp hc
  rw [hp]
  refine ⟨.int 1 (LLVM.Int.icmp x (LLVM.Int.or x y true) .ne),
    (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
  simpa only [LLVM.Int.cast_self, icmp_or_ult_ne_swapped_disjoint] using
    (isRefinedBy_refl (LLVM.Int.icmp x (LLVM.Int.or x y true) .ne))

end Veir.Passes.InstCombineLLVM.OrUgtToNe
