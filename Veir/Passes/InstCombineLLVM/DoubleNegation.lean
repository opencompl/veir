module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Data.LLVM.Int.Basic

namespace Veir.Passes.InstCombineLLVM.DoubleNegation

open Veir
open Veir.Data
open Veir.Puddle
open Veir.Passes.InstCombineLLVM

/-- Lean 4.35 `cbv` workaround specialized to the guard result type used by the checker. -/
@[local cbv_eval]
theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

/-- Scalar specialization of InstCombineNegator.cpp:122-124. -/
public def doubleNegation : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let innerZero ← matchIntConstant ty 0
      let inner ← MatchProg.operation (.llvm .sub) #[innerZero, x] #[ty]
        (fun _ => true)
      let outerZero ← matchIntConstant ty 0
      let _ ← MatchProg.root (.llvm .sub) #[outerZero, inner.res[0]!] #[ty]
        (fun _ => true)
      return x)
    pure
    (fun x => x)

public theorem doubleNegation_valid : Pattern.Valid doubleNegation := by
  simp only [doubleNegation, matchIntConstant]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index,
    forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x
  rintro ⟨innerZeroValue⟩ innerZero hInnerZero hinterpInnerZero
  cases innerZeroValue with
  | float _ | dense _ | string _ => simp at hInnerZero
  | integer innerZeroAttr =>
    have hInnerZeroValue : innerZeroAttr.value = 0 := of_decide_eq_true hInnerZero
    obtain rfl := (constant_iff _ innerZeroAttr _).mp hinterpInnerZero
    rintro innerProps inner hinterpInner
    obtain rfl := (sub_iff _ _ _ _ _).mp hinterpInner
    rintro ⟨outerZeroValue⟩ outerZero hOuterZero hinterpOuterZero
    cases outerZeroValue with
    | float _ | dense _ | string _ => simp at hOuterZero
    | integer outerZeroAttr =>
      have hOuterZeroValue : outerZeroAttr.value = 0 := of_decide_eq_true hOuterZero
      obtain rfl := (constant_iff _ outerZeroAttr _).mp hinterpOuterZero
      rintro outerProps result hinterpOuter
      obtain rfl := (sub_iff _ _ _ _ _).mp hinterpOuter
      rw [hInnerZeroValue, hOuterZeroValue]
      change ∃ h : w = w,
        (LLVM.Int.sub (.val (BitVec.ofInt w 0))
          (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x innerProps.nsw innerProps.nuw)
          outerProps.nsw outerProps.nuw).cast h ⊒ x
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        (double_neg_refines w x innerProps.nsw innerProps.nuw outerProps.nsw outerProps.nuw)

end Veir.Passes.InstCombineLLVM.DoubleNegation
