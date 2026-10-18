module
public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.AddNegLeft
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl

/-- Scalar specialization of InstCombineAddSub.cpp:1672-1678: `(-A)+B -> B-A`.
    This conservative form clears result flags. -/
public def addNegLeft : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let negA ← MatchProg.operation (.llvm .sub) #[zero, a] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .add) #[negA.res[0]!, b] #[ty] (fun _ => true)
    return (ty, b, a))
  (fun (ty, b, a) => do
    let props ← CreateProg.property (.llvm .sub) default
    CreateProg.operation (.llvm .sub) #[b, a] #[ty] props)
  (fun result => result.res[0]!)

public theorem addNegLeft_valid : Pattern.Valid addNegLeft := by
  simp only [addNegLeft, matchIntConstant]; unfoldPuddleBuilder
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
    rintro negProps negA hNegA
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegA
    rintro addProps source hSource
    obtain rfl := (add_iff _ _ _ _ _).mp hSource
    rw [hzv]
    refine ⟨.int w (LLVM.Int.sub b a), (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (add_neg_left_refines w a b negProps.nsw negProps.nuw addProps.nsw addProps.nuw)

/-- NSW-preserving scalar form emitted when both the negation and add are NSW. -/
public def addNegLeftNSW : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let negA ← MatchProg.operation (.llvm .sub) #[zero, a] #[ty] (fun p => p.nsw)
    let _ ← MatchProg.root (.llvm .add) #[negA.res[0]!, b] #[ty] (fun p => p.nsw)
    return (ty, b, a))
  (fun (ty, b, a) => do
    let props ← CreateProg.property (.llvm .sub) { nsw := true, nuw := false }
    CreateProg.operation (.llvm .sub) #[b, a] #[ty] props)
  (fun result => result.res[0]!)

public theorem addNegLeftNSW_valid : Pattern.Valid addNegLeftNSW := by
  simp only [addNegLeftNSW, matchIntConstant]; unfoldPuddleBuilder
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
    rintro negProps negA hNegNSW hNegA
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegA
    rintro addProps source hAddNSW hSource
    obtain rfl := (add_iff _ _ _ _ _).mp hSource
    rw [hZeroValue, hNegNSW, hAddNSW]
    refine ⟨.int w (LLVM.Int.sub b a true false), (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (add_neg_left_nsw_refines w a b negProps.nuw addProps.nuw)
end Veir.Passes.InstCombineLLVM.AddNegLeft
