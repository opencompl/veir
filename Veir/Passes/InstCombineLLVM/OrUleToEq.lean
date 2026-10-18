module

public import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.OrUleToEq

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

/-- Arbitrary-width, non-disjoint scalar specialization of InstCombineCompares.cpp:5256-5265:
    `(X | Y) ule X -> (X | Y) eq X`. -/
public def orUleToEq : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let orOp ← MatchProg.operation (.llvm .or) #[x, y] #[ty]
        (fun props => props.disjoint = false)
      let _ ← MatchProg.root (.llvm .icmp) #[orOp.res[0]!, x] #[boolTy]
        (fun props => props.predicate = .ule)
      return (boolTy, orOp.res[0]!, x))
    (fun (boolTy, lhs, rhs) => do
      let props ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .eq)
      CreateProg.operation (.llvm .icmp) #[lhs, rhs] #[boolTy] props)
    (fun result => result.res[0]!)

public theorem orUleToEq_valid : Pattern.Valid orUleToEq := by
  simp only [orUleToEq]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.insertFreshBindings,
        CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩
  rintro boolType ⟨boolW, boolSignedness⟩ hBoolType hBoolWidth
  subst boolType
  change boolW = 1 at hBoolWidth
  subst boolW
  rintro x y
  rintro sourceOrProps sourceOr hDisjoint hSourceOr
  obtain rfl := (or_iff _ sourceOrProps _ _ _).mp hSourceOr
  have hd : sourceOrProps.disjoint = false := hDisjoint
  rw [hd]
  rintro sourceProps source hPredicate hSource
  obtain rfl := (icmp_iff _ sourceProps _ _ _).mp hSource
  rw [hPredicate]
  refine ⟨.int 1 (LLVM.Int.icmp (LLVM.Int.or x y false) x .eq),
    (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, icmp_or_ule_eq] using
    (isRefinedBy_refl (LLVM.Int.icmp (LLVM.Int.or x y false) x .eq))


/-- Symmetric compare orientation accepted by the same LLVM source branch. -/
public def orUleToEqSwapped : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let orOp ← MatchProg.operation (.llvm .or) #[x, y] #[ty]
        (fun props => props.disjoint = false)
      let _ ← MatchProg.root (.llvm .icmp) #[x, orOp.res[0]!] #[boolTy]
        (fun props => props.predicate = .uge)
      return (boolTy, x, orOp.res[0]!))
    (fun (boolTy, lhs, rhs) => do
      let props ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .eq)
      CreateProg.operation (.llvm .icmp) #[lhs, rhs] #[boolTy] props)
    (fun result => result.res[0]!)

public theorem orUleToEqSwapped_valid : Pattern.Valid orUleToEqSwapped := by
  simp only [orUleToEqSwapped]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.insertFreshBindings,
        CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩
  rintro boolType ⟨boolW, boolSignedness⟩ hBoolType hBoolWidth
  subst boolType
  change boolW = 1 at hBoolWidth
  subst boolW
  rintro x y
  rintro sourceOrProps sourceOr hDisjoint hSourceOr
  obtain rfl := (or_iff _ sourceOrProps _ _ _).mp hSourceOr
  have hd : sourceOrProps.disjoint = false := hDisjoint
  rw [hd]
  rintro sourceProps source hPredicate hSource
  obtain rfl := (icmp_iff _ sourceProps _ _ _).mp hSource
  rw [hPredicate]
  refine ⟨.int 1 (LLVM.Int.icmp x (LLVM.Int.or x y false) .eq),
    (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, icmp_or_uge_eq_swapped] using
    (isRefinedBy_refl (LLVM.Int.icmp x (LLVM.Int.or x y false) .eq))


/-- Disjoint-flag specialization of the same source shape. -/
public def orUleToEqDisjoint : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let orOp ← MatchProg.operation (.llvm .or) #[x, y] #[ty]
        (fun props => props.disjoint = true)
      let _ ← MatchProg.root (.llvm .icmp) #[orOp.res[0]!, x] #[boolTy]
        (fun props => props.predicate = .ule)
      return (boolTy, orOp.res[0]!, x))
    (fun (boolTy, lhs, rhs) => do
      let props ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .eq)
      CreateProg.operation (.llvm .icmp) #[lhs, rhs] #[boolTy] props)
    (fun result => result.res[0]!)

public theorem orUleToEqDisjoint_valid : Pattern.Valid orUleToEqDisjoint := by
  simp only [orUleToEqDisjoint]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.insertFreshBindings,
        CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩
  rintro boolType ⟨boolW, boolSignedness⟩ hBoolType hBoolWidth
  subst boolType
  change boolW = 1 at hBoolWidth
  subst boolW
  rintro x y
  rintro sourceOrProps sourceOr hDisjoint hSourceOr
  obtain rfl := (or_iff _ sourceOrProps _ _ _).mp hSourceOr
  have hd : sourceOrProps.disjoint = true := hDisjoint
  rw [hd]
  rintro sourceProps source hPredicate hSource
  obtain rfl := (icmp_iff _ sourceProps _ _ _).mp hSource
  rw [hPredicate]
  refine ⟨.int 1 (LLVM.Int.icmp (LLVM.Int.or x y true) x .eq),
    (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, icmp_or_ule_eq_disjoint] using
    (isRefinedBy_refl (LLVM.Int.icmp (LLVM.Int.or x y true) x .eq))


/-- Disjoint-flag specialization of the same source shape. -/
public def orUleToEqSwappedDisjoint : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let orOp ← MatchProg.operation (.llvm .or) #[x, y] #[ty]
        (fun props => props.disjoint = true)
      let _ ← MatchProg.root (.llvm .icmp) #[x, orOp.res[0]!] #[boolTy]
        (fun props => props.predicate = .uge)
      return (boolTy, x, orOp.res[0]!))
    (fun (boolTy, lhs, rhs) => do
      let props ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .eq)
      CreateProg.operation (.llvm .icmp) #[lhs, rhs] #[boolTy] props)
    (fun result => result.res[0]!)

public theorem orUleToEqSwappedDisjoint_valid : Pattern.Valid orUleToEqSwappedDisjoint := by
  simp only [orUleToEqSwappedDisjoint]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.insertFreshBindings,
        CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩
  rintro boolType ⟨boolW, boolSignedness⟩ hBoolType hBoolWidth
  subst boolType
  change boolW = 1 at hBoolWidth
  subst boolW
  rintro x y
  rintro sourceOrProps sourceOr hDisjoint hSourceOr
  obtain rfl := (or_iff _ sourceOrProps _ _ _).mp hSourceOr
  have hd : sourceOrProps.disjoint = true := hDisjoint
  rw [hd]
  rintro sourceProps source hPredicate hSource
  obtain rfl := (icmp_iff _ sourceProps _ _ _).mp hSource
  rw [hPredicate]
  refine ⟨.int 1 (LLVM.Int.icmp x (LLVM.Int.or x y true) .eq),
    (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, icmp_or_uge_eq_swapped_disjoint] using
    (isRefinedBy_refl (LLVM.Int.icmp x (LLVM.Int.or x y true) .eq))

end Veir.Passes.InstCombineLLVM.OrUleToEq
