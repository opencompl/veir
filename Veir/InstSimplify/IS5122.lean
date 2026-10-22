import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 16000000
/-- Exact constant selection over all modeled scalar literals, zero markers and poison constants. -/
def IS5122 (resultType : IntegerType) (cond trueVal falseVal : ScalarLiteral) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t == resultType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let c ← matchScalarLiteral cty cond
    let t ← matchScalarLiteral ty trueVal
    let f ← matchScalarLiteral ty falseVal
    let _ ← MatchProg.root (.llvm .select) #[c,t,f] #[ty]
    return ty)
  (fun ty => createScalarLiteral ty (foldSelectLiteral cond trueVal falseVal) resultType)
  (fun x => x)

theorem IS5122_valid (resultType : IntegerType) (cond trueVal falseVal : ScalarLiteral) :
    Pattern.Valid (IS5122 resultType cond trueVal falseVal) := by
  rcases resultType with ⟨w,s⟩
  cases cond with
  | integer n =>
    cases hcnd : (BitVec.ofInt 1 n == 1#1)
    all_goals
      cases trueVal <;> cases falseVal
      all_goals
        simp only [IS5122, matchScalarLiteral, createScalarLiteral, foldSelectLiteral,
          matchIntConstant, matchZero, matchPoison]
        simp only [hcnd, Bool.false_eq_true, ↓reduceIte]
        provePuddleValid
        rintro _ ty rfl ht _ ⟨cw,cs⟩ rfl hc
        have : ty = IntegerType.mk w s := by simpa using ht
        subst ty
        have : cw = 1 := by simpa using hc
        subst cw
        first
        | rintro cp cv ch ci
          obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
        | rintro cp cv ci
          first | obtain rfl := (zero_iff _ _ _).mp ci
                | obtain rfl := (poison_iff _ _ _).mp ci
        first
        | rintro tp tv th ti
          obtain rfl := (matched_constant_iff _ _ _ th _).mp ti
        | rintro tp tv ti
          first | obtain rfl := (zero_iff _ _ _).mp ti
                | obtain rfl := (poison_iff _ _ _).mp ti
        first
        | rintro fp fv fh fi
          obtain rfl := (matched_constant_iff _ _ _ fh _).mp fi
        | rintro fp fv fi
          first | obtain rfl := (zero_iff _ _ _).mp fi
                | obtain rfl := (poison_iff _ _ _).mp fi
        rintro rp rv ri
        obtain rfl := (select_iff _ _ _ _ _ _).mp ri
        first
        | refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
        | refine ⟨_, (zero_iff _ _ _).mpr rfl, ?_⟩
        | refine ⟨_, (poison_iff _ _ _).mpr rfl, ?_⟩
        simp [LLVM.Int.select, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy, hcnd]
  | zero =>
    cases trueVal <;> cases falseVal
    all_goals
      simp only [IS5122, matchScalarLiteral, createScalarLiteral, foldSelectLiteral,
        matchIntConstant, matchZero, matchPoison]
      skip
      provePuddleValid
      rintro _ ty rfl ht _ ⟨cw,cs⟩ rfl hc
      have : ty = IntegerType.mk w s := by simpa using ht
      subst ty
      have : cw = 1 := by simpa using hc
      subst cw
      first
      | rintro cp cv ch ci
        obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
      | rintro cp cv ci
        first | obtain rfl := (zero_iff _ _ _).mp ci
              | obtain rfl := (poison_iff _ _ _).mp ci
      first
      | rintro tp tv th ti
        obtain rfl := (matched_constant_iff _ _ _ th _).mp ti
      | rintro tp tv ti
        first | obtain rfl := (zero_iff _ _ _).mp ti
              | obtain rfl := (poison_iff _ _ _).mp ti
      first
      | rintro fp fv fh fi
        obtain rfl := (matched_constant_iff _ _ _ fh _).mp fi
      | rintro fp fv fi
        first | obtain rfl := (zero_iff _ _ _).mp fi
              | obtain rfl := (poison_iff _ _ _).mp fi
      rintro rp rv ri
      obtain rfl := (select_iff _ _ _ _ _ _).mp ri
      first
      | refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
      | refine ⟨_, (zero_iff _ _ _).mpr rfl, ?_⟩
      | refine ⟨_, (poison_iff _ _ _).mpr rfl, ?_⟩
      simp [LLVM.Int.select, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | poison =>
    cases trueVal <;> cases falseVal
    all_goals
      simp only [IS5122, matchScalarLiteral, createScalarLiteral, foldSelectLiteral,
        matchIntConstant, matchZero, matchPoison]
      skip
      provePuddleValid
      rintro _ ty rfl ht _ ⟨cw,cs⟩ rfl hc
      have : ty = IntegerType.mk w s := by simpa using ht
      subst ty
      have : cw = 1 := by simpa using hc
      subst cw
      first
      | rintro cp cv ch ci
        obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
      | rintro cp cv ci
        first | obtain rfl := (zero_iff _ _ _).mp ci
              | obtain rfl := (poison_iff _ _ _).mp ci
      first
      | rintro tp tv th ti
        obtain rfl := (matched_constant_iff _ _ _ th _).mp ti
      | rintro tp tv ti
        first | obtain rfl := (zero_iff _ _ _).mp ti
              | obtain rfl := (poison_iff _ _ _).mp ti
      first
      | rintro fp fv fh fi
        obtain rfl := (matched_constant_iff _ _ _ fh _).mp fi
      | rintro fp fv fi
        first | obtain rfl := (zero_iff _ _ _).mp fi
              | obtain rfl := (poison_iff _ _ _).mp fi
      rintro rp rv ri
      obtain rfl := (select_iff _ _ _ _ _ _).mp ri
      first
      | refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
      | refine ⟨_, (zero_iff _ _ _).mpr rfl, ?_⟩
      | refine ⟨_, (poison_iff _ _ _).mpr rfl, ?_⟩
      simp [LLVM.Int.select, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
