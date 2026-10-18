module

public import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.AndUgeToEq

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

/-- Arbitrary-width scalar specialization of InstCombineCompares.cpp:5203-5207:
    `(X & Y) uge X -> (X & Y) eq X`. -/
public def andUgeToEq : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let andOp ← MatchProg.operation (.llvm .and) #[x, y] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .icmp) #[andOp.res[0]!, x] #[boolTy]
        (fun props => props.predicate = .uge)
      return (boolTy, andOp.res[0]!, x))
    (fun (boolTy, lhs, rhs) => do
      let props ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .eq)
      CreateProg.operation (.llvm .icmp) #[lhs, rhs] #[boolTy] props)
    (fun result => result.res[0]!)

public theorem andUgeToEq_valid : Pattern.Valid andUgeToEq := by
  simp only [andUgeToEq]
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
  rintro ⟨⟩ sourceAnd hSourceAnd
  obtain rfl := (and_iff _ _ _ _).mp hSourceAnd
  rintro sourceProps source hPredicate hSource
  obtain rfl := (icmp_iff _ sourceProps _ _ _).mp hSource
  rw [hPredicate]
  refine ⟨.int 1 (LLVM.Int.icmp (LLVM.Int.and x y) x .eq),
    (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, icmp_and_uge_eq] using
    (isRefinedBy_refl (LLVM.Int.icmp (LLVM.Int.and x y) x .eq))


/-- Symmetric compare orientation accepted by the same LLVM source branch. -/
public def andUgeToEqSwapped : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let andOp ← MatchProg.operation (.llvm .and) #[x, y] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .icmp) #[x, andOp.res[0]!] #[boolTy]
        (fun props => props.predicate = .ule)
      return (boolTy, x, andOp.res[0]!))
    (fun (boolTy, lhs, rhs) => do
      let props ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .eq)
      CreateProg.operation (.llvm .icmp) #[lhs, rhs] #[boolTy] props)
    (fun result => result.res[0]!)

public theorem andUgeToEqSwapped_valid : Pattern.Valid andUgeToEqSwapped := by
  simp only [andUgeToEqSwapped]
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
  rintro ⟨⟩ sourceAnd hSourceAnd
  obtain rfl := (and_iff _ _ _ _).mp hSourceAnd
  rintro sourceProps source hPredicate hSource
  obtain rfl := (icmp_iff _ sourceProps _ _ _).mp hSource
  rw [hPredicate]
  refine ⟨.int 1 (LLVM.Int.icmp x (LLVM.Int.and x y) .eq),
    (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, icmp_and_ule_eq_swapped] using
    (isRefinedBy_refl (LLVM.Int.icmp x (LLVM.Int.and x y) .eq))

end Veir.Passes.InstCombineLLVM.AndUgeToEq
