module
public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.AddNegRight
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl

/-- Scalar specialization of InstCombineAddSub.cpp:1680-1686: `A+(-B) -> A-B`.
    This conservative form clears result flags. -/
public def addNegRight : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let negB ← MatchProg.operation (.llvm .sub) #[zero, b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .add) #[a, negB.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .sub) default
    CreateProg.operation (.llvm .sub) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem addNegRight_valid : Pattern.Valid addNegRight := by
  simp only [addNegRight, matchIntConstant]; unfoldPuddleBuilder
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
  rintro ⟨cv⟩ zero hz hiz
  cases cv with
  | float _ | dense _ | string _ => simp at hz
  | integer za =>
    have hzv : za.value = 0 := of_decide_eq_true hz
    obtain rfl := (constant_iff _ za _).mp hiz
    rintro negProps negB hNegB
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegB
    rintro addProps source hSource
    obtain rfl := (add_iff _ _ _ _ _).mp hSource
    rw [hzv]
    refine ⟨.int w (LLVM.Int.sub a b), (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (add_neg_right_refines w a b negProps.nsw negProps.nuw addProps.nsw addProps.nuw)

/-- NSW-preserving scalar form emitted when both the negation and add are NSW. -/
public def addNegRightNSW : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let negB ← MatchProg.operation (.llvm .sub) #[zero, b] #[ty] (fun p => p.nsw)
    let _ ← MatchProg.root (.llvm .add) #[a, negB.res[0]!] #[ty] (fun p => p.nsw)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let props ← CreateProg.property (.llvm .sub) { nsw := true, nuw := false }
    CreateProg.operation (.llvm .sub) #[a, b] #[ty] props)
  (fun result => result.res[0]!)

public theorem addNegRightNSW_valid : Pattern.Valid addNegRightNSW := by
  simp only [addNegRightNSW, matchIntConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ a b
  rintro ⟨constantValue⟩ zero hZero hInterpZero
  cases constantValue with
  | float _ | dense _ | string _ => simp at hZero
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro negProps negB hNegNSW hNegB
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegB
    rintro addProps source hAddNSW hSource
    obtain rfl := (add_iff _ _ _ _ _).mp hSource
    rw [hZeroValue, hNegNSW, hAddNSW]
    refine ⟨.int w (LLVM.Int.sub a b true false), (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (add_neg_right_nsw_refines w a b negProps.nuw addProps.nuw)
end Veir.Passes.InstCombineLLVM.AddNegRight
