module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.MulSinkNeg

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def mulSinkNegPattern (rootCommuted : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let zero ← matchIntConstant ty 0
      let negX ← MatchProg.operation (.llvm .sub) #[zero, x] #[ty] (fun _ => true)
      let _ ← if rootCommuted then
        MatchProg.root (.llvm .mul) #[y, negX.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .mul) #[negX.res[0]!, y] #[ty] (fun _ => true)
      return (ty, x, y, zero))
    (fun (ty, x, y, zero) => do
      let mp ← CreateProg.property (.llvm .mul) default
      let product ← CreateProg.operation (.llvm .mul) #[x, y] #[ty] mp
      let sp ← CreateProg.property (.llvm .sub) default
      CreateProg.operation (.llvm .sub) #[zero, product.res[0]!] #[ty] sp)
    (fun result => result.res[0]!)

private theorem mulSinkNegPattern_valid (rootCommuted : Bool) :
    Pattern.Valid (mulSinkNegPattern rootCommuted) := by
  cases rootCommuted <;> simp only [mulSinkNegPattern, matchIntConstant,
      Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
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
    rintro ⟨zeroValue⟩ zero hZero hInterpZero
    cases zeroValue with
    | float _ | dense _ | string _ => simp at hZero
    | integer zeroAttr =>
      have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
      obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
      rintro negProps negX hNegX
      obtain rfl := (sub_iff _ _ _ _ _).mp hNegX
      rintro mulProps source hSource
      obtain rfl := (mul_iff _ _ _ _ _).mp hSource
      rw [hZeroValue]
      refine ⟨.int w (LLVM.Int.mul x y), (mul_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.sub (.val (BitVec.ofInt w 0)) (LLVM.Int.mul x y)),
        (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      first
      | simpa only [LLVM.Int.cast_self] using
          (mul_neg_left_flags_refine w x y negProps.nsw negProps.nuw
            mulProps.nsw mulProps.nuw)
      | simpa only [LLVM.Int.cast_self] using
          (mul_neg_right_flags_refine w y x negProps.nsw negProps.nuw
            mulProps.nsw mulProps.nuw)

/- Scalar semantic specialization of InstCombineMulDivRem.cpp:435-438.
   Puddle currently omits the source's profitability-only one-use guard. -/
public def mulSinkNeg : Pattern OpCode := mulSinkNegPattern false
public theorem mulSinkNeg_valid : Pattern.Valid mulSinkNeg :=
  mulSinkNegPattern_valid false

public def mulSinkNegCommuted : Pattern OpCode := mulSinkNegPattern true
public theorem mulSinkNegCommuted_valid : Pattern.Valid mulSinkNegCommuted :=
  mulSinkNegPattern_valid true

end Veir.Passes.InstCombineLLVM.MulSinkNeg
