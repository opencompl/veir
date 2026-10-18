module
public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.NegateI1
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl
public def negateI1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    MatchProg.matchNative ty fun type =>
      match type.cast? IntegerType with | some t => t.bitwidth = 1 | none => false
    let x ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let _ ← MatchProg.root (.llvm .sub) #[zero,x] #[ty] (fun _ => true)
    return x) pure (fun x => x)
public theorem negateI1_valid : Pattern.Valid negateI1 := by
  simp only [negateI1, matchIntConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x
  rintro ⟨zv⟩ z hz hiz
  cases zv with
  | float _ | dense _ | string _ => simp at hz
  | integer za =>
    have hzv : za.value = 0 := of_decide_eq_true hz
    obtain rfl := (constant_iff _ za _).mp hiz
    rintro props result hir hw
    obtain rfl := (sub_iff _ _ _ _ _).mp hir
    rw [hzv]
    simp only [IsTypeAttr.cast?_of] at hw
    have hw' : w = 1 := of_decide_eq_true hw
    subst w
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using neg_i1_refines x props.nsw props.nuw
end Veir.Passes.InstCombineLLVM.NegateI1
