module
public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.SubSwap
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl

/-- Scalar specialization of InstCombineNegator.cpp:215-226: `-(a-b) -> b-a`. -/
public def subSwap : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty
    let inner ← MatchProg.operation (.llvm .sub) #[a,b] #[ty] (fun _ => true)
    let zero ← matchIntConstant ty 0
    let _ ← MatchProg.root (.llvm .sub) #[zero,inner.res[0]!] #[ty] (fun _ => true)
    return (ty,a,b))
  (fun (ty,a,b) => do
    let props ← CreateProg.property (.llvm .sub) default
    CreateProg.operation (.llvm .sub) #[b,a] #[ty] props)
  (fun op => op.res[0]!)

public theorem subSwap_valid : Pattern.Valid subSwap := by
  simp only [subSwap, matchIntConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a b innerProps inner hinterpInner
  obtain rfl := (sub_iff _ _ _ _ _).mp hinterpInner
  rintro ⟨zv⟩ z hz hiz
  cases zv with
  | float _ | dense _ | string _ => simp at hz
  | integer za =>
    have hzv : za.value = 0 := of_decide_eq_true hz
    obtain rfl := (constant_iff _ za _).mp hiz
    rintro outerProps result hir
    obtain rfl := (sub_iff _ _ _ _ _).mp hir
    rw [hzv]
    refine ⟨.int w (LLVM.Int.sub b a), ?_, ?_⟩
    · exact (sub_iff _ _ _ _ _).mpr rfl
    change ∃ h : w=w, (LLVM.Int.sub (.val (BitVec.ofInt w 0))
      (LLVM.Int.sub a b innerProps.nsw innerProps.nuw) outerProps.nsw outerProps.nuw).cast h ⊒
      LLVM.Int.sub b a
    exact ⟨rfl, by simpa using neg_sub_refines w a b innerProps.nsw innerProps.nuw outerProps.nsw outerProps.nuw⟩

/-- Exact NSW-propagating form emitted when both matched subtractions are NSW. -/
public def subSwapNSW : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty
    let inner ← MatchProg.operation (.llvm .sub) #[a,b] #[ty] (fun p => p.nsw)
    let zero ← matchIntConstant ty 0
    let _ ← MatchProg.root (.llvm .sub) #[zero,inner.res[0]!] #[ty] (fun p => p.nsw)
    return (ty,a,b))
  (fun (ty,a,b) => do
    let props ← CreateProg.property (.llvm .sub) { nsw := true, nuw := false }
    CreateProg.operation (.llvm .sub) #[b,a] #[ty] props)
  (fun op => op.res[0]!)

public theorem subSwapNSW_valid : Pattern.Valid subSwapNSW := by
  simp only [subSwapNSW, matchIntConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a b innerProps inner hInnerNSW hinterpInner
  obtain rfl := (sub_iff _ _ _ _ _).mp hinterpInner
  rintro ⟨zv⟩ z hz hiz
  cases zv with
  | float _ | dense _ | string _ => simp at hz
  | integer za =>
    have hzv : za.value = 0 := of_decide_eq_true hz
    obtain rfl := (constant_iff _ za _).mp hiz
    rintro outerProps result hOuterNSW hir
    obtain rfl := (sub_iff _ _ _ _ _).mp hir
    rw [hzv, hInnerNSW, hOuterNSW]
    refine ⟨.int w (LLVM.Int.sub b a true false), ?_, ?_⟩
    · exact (sub_iff _ _ _ _ _).mpr rfl
    change ∃ h : w=w, (LLVM.Int.sub (.val (BitVec.ofInt w 0))
      (LLVM.Int.sub a b true innerProps.nuw) true outerProps.nuw).cast h ⊒
      LLVM.Int.sub b a true false
    exact ⟨rfl, by simpa using neg_sub_nsw_refines w a b innerProps.nuw outerProps.nuw⟩
end Veir.Passes.InstCombineLLVM.SubSwap
