module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.MulDoubleNeg

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

/- HasNSW-disabled specialization of InstCombineMulDivRem.cpp:426-432. -/
public def mulDoubleNeg : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let zeroX ← matchIntConstant ty 0
      let negX ← MatchProg.operation (.llvm .sub) #[zeroX, x] #[ty] (fun _ => true)
      let zeroY ← matchIntConstant ty 0
      let negY ← MatchProg.operation (.llvm .sub) #[zeroY, y] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .mul) #[negX.res[0]!, negY.res[0]!] #[ty]
        (fun _ => true)
      return (ty, x, y))
    (fun (ty, x, y) => do
      let mp ← CreateProg.property (.llvm .mul) default
      CreateProg.operation (.llvm .mul) #[x, y] #[ty] mp)
    (fun result => result.res[0]!)

public theorem mulDoubleNeg_valid : Pattern.Valid mulDoubleNeg := by
  simp only [mulDoubleNeg, matchIntConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ x y
  rintro ⟨zeroXValue⟩ zeroX hZeroX hInterpZeroX
  cases zeroXValue with
  | float _ | dense _ | string _ => simp at hZeroX
  | integer zeroXAttr =>
    have hZeroXValue : zeroXAttr.value = 0 := of_decide_eq_true hZeroX
    obtain rfl := (constant_iff _ zeroXAttr _).mp hInterpZeroX
    rintro negXProps negX hNegX
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegX
    rintro ⟨zeroYValue⟩ zeroY hZeroY hInterpZeroY
    cases zeroYValue with
    | float _ | dense _ | string _ => simp at hZeroY
    | integer zeroYAttr =>
      have hZeroYValue : zeroYAttr.value = 0 := of_decide_eq_true hZeroY
      obtain rfl := (constant_iff _ zeroYAttr _).mp hInterpZeroY
      rintro negYProps negY hNegY
      obtain rfl := (sub_iff _ _ _ _ _).mp hNegY
      rintro mulProps source hSource
      obtain rfl := (mul_iff _ _ _ _ _).mp hSource
      rw [hZeroXValue, hZeroYValue]
      refine ⟨.int w (LLVM.Int.mul x y), (mul_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        (mul_neg_neg_flags_refine w x y negXProps.nsw negXProps.nuw
          negYProps.nsw negYProps.nuw mulProps.nsw mulProps.nuw)

/-- NSW-preserving form emitted when both negations and the source multiplication are NSW. -/
public def mulDoubleNegNSW : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let zeroX ← matchIntConstant ty 0
    let negX ← MatchProg.operation (.llvm .sub) #[zeroX, x] #[ty] (fun p => p.nsw)
    let zeroY ← matchIntConstant ty 0
    let negY ← MatchProg.operation (.llvm .sub) #[zeroY, y] #[ty] (fun p => p.nsw)
    let _ ← MatchProg.root (.llvm .mul) #[negX.res[0]!, negY.res[0]!] #[ty]
      (fun p => p.nsw)
    return (ty, x, y))
  (fun (ty, x, y) => do
    let props ← CreateProg.property (.llvm .mul) { nsw := true, nuw := false }
    CreateProg.operation (.llvm .mul) #[x, y] #[ty] props)
  (fun result => result.res[0]!)

public theorem mulDoubleNegNSW_valid : Pattern.Valid mulDoubleNegNSW := by
  simp only [mulDoubleNegNSW, matchIntConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x y
  rintro ⟨zeroXValue⟩ zeroX hZeroX hInterpZeroX
  cases zeroXValue with
  | float _ | dense _ | string _ => simp at hZeroX
  | integer zeroXAttr =>
    have hZeroXValue : zeroXAttr.value = 0 := of_decide_eq_true hZeroX
    obtain rfl := (constant_iff _ zeroXAttr _).mp hInterpZeroX
    rintro negXProps negX hNegXNSW hNegX
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegX
    rintro ⟨zeroYValue⟩ zeroY hZeroY hInterpZeroY
    cases zeroYValue with
    | float _ | dense _ | string _ => simp at hZeroY
    | integer zeroYAttr =>
      have hZeroYValue : zeroYAttr.value = 0 := of_decide_eq_true hZeroY
      obtain rfl := (constant_iff _ zeroYAttr _).mp hInterpZeroY
      rintro negYProps negY hNegYNSW hNegY
      obtain rfl := (sub_iff _ _ _ _ _).mp hNegY
      rintro mulProps source hMulNSW hSource
      obtain rfl := (mul_iff _ _ _ _ _).mp hSource
      rw [hZeroXValue, hZeroYValue, hNegXNSW, hNegYNSW, hMulNSW]
      refine ⟨.int w (LLVM.Int.mul x y true false), (mul_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        (mul_neg_neg_nsw_refines w x y negXProps.nuw negYProps.nuw mulProps.nuw)

end Veir.Passes.InstCombineLLVM.MulDoubleNeg
