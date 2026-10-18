module
public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.AddNegNeg
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl

/-- Scalar specialization of InstCombineAddSub.cpp:1666-1671: `(-A)+(-B) -> -(A+B)`. -/
public def addNegNeg : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let zeroA ← matchIntConstant ty 0
    let negA ← MatchProg.operation (.llvm .sub) #[zeroA, a] #[ty] (fun _ => true)
    let zeroB ← matchIntConstant ty 0
    let negB ← MatchProg.operation (.llvm .sub) #[zeroB, b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .add) #[negA.res[0]!, negB.res[0]!] #[ty] (fun _ => true)
    return (ty, zeroA, a, b))
  (fun (ty, zero, a, b) => do
    let addProps ← CreateProg.property (.llvm .add) default
    let sum ← CreateProg.operation (.llvm .add) #[a, b] #[ty] addProps
    let subProps ← CreateProg.property (.llvm .sub) default
    CreateProg.operation (.llvm .sub) #[zero, sum.res[0]!] #[ty] subProps)
  (fun result => result.res[0]!)

public theorem addNegNeg_valid : Pattern.Valid addNegNeg := by
  simp only [addNegNeg, matchIntConstant]; unfoldPuddleBuilder
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
  rintro ⟨cvA⟩ zeroA hzA hizA
  cases cvA with
  | float _ | dense _ | string _ => simp at hzA
  | integer za =>
    have hzAv : za.value = 0 := of_decide_eq_true hzA
    obtain rfl := (constant_iff _ za _).mp hizA
    rintro negAProps negA hNegA
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegA
    rintro ⟨cvB⟩ zeroB hzB hizB
    cases cvB with
    | float _ | dense _ | string _ => simp at hzB
    | integer zb =>
      have hzBv : zb.value = 0 := of_decide_eq_true hzB
      obtain rfl := (constant_iff _ zb _).mp hizB
      rintro negBProps negB hNegB
      obtain rfl := (sub_iff _ _ _ _ _).mp hNegB
      rintro addProps source hSource
      obtain rfl := (add_iff _ _ _ _ _).mp hSource
      rw [hzAv, hzBv]
      refine ⟨.int w (LLVM.Int.add a b), (add_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.sub (.val (BitVec.ofInt w 0)) (LLVM.Int.add a b)),
        (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        (add_neg_neg_refines w a b negAProps.nsw negAProps.nuw
          negBProps.nsw negBProps.nuw addProps.nsw addProps.nuw)
end Veir.Passes.InstCombineLLVM.AddNegNeg
