module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.OrAndNotOr

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def orAndNotOrPattern (orCommuted notConstantLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let both ← MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
      let either ← if orCommuted then
        MatchProg.operation (.llvm .or) #[b, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[a, b] #[ty] (fun _ => true)
      let notEither ← if notConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, either.res[0]!]
          #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[either.res[0]!, minusOne]
          #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .or) #[both.res[0]!, notEither.res[0]!]
        #[ty] (fun _ => true)
      return (ty, a, b, minusOne))
    (fun (ty, a, b, minusOne) => do
      let xp ← CreateProg.property (.llvm .xor) ()
      let xor ← CreateProg.operation (.llvm .xor) #[a, b] #[ty] xp
      let np ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[xor.res[0]!, minusOne] #[ty] np)
    (fun result => result.res[0]!)

private theorem orAndNotOrPattern_valid (orCommuted notConstantLeft : Bool) :
    Pattern.Valid (orAndNotOrPattern orCommuted notConstantLeft) := by
  cases orCommuted <;> cases notConstantLeft <;>
    simp only [orAndNotOrPattern, matchIntConstantNormalized,
      Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [properties_of, guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup,
        HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
        HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.requireBindings, MetadataTuple.Shape.insertFreshBindings,
        IsMetadataTuple.shape_property, CreateProg.checkBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
    simpScalarPropertyPuddleSemantics
    rintro ⟨w, s⟩ a b
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      simp [isNormalizedIntConstant, asLLVMConstantProperties]
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ both hBoth
      obtain rfl := (and_iff _ _ _ _).mp hBoth
      rintro innerProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
      rintro ⟨⟩ notEither hNotEither
      obtain rfl := (xor_iff _ _ _ _).mp hNotEither
      rintro outerProps source hSource
      obtain rfl := (or_iff _ _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor (LLVM.Int.xor a b) (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_or_comm, llvm_xor_comm] using
        (and_or_not_or_refines_not_xor w a b
          innerProps.disjoint outerProps.disjoint)

/- Scalar semantic specialization of InstCombineAndOrXor.cpp:1980-1983.
   Puddle currently omits the source's profitability-only one-use guard. -/
public def orAndNotOr : Pattern OpCode := orAndNotOrPattern false false

public theorem orAndNotOr_valid : Pattern.Valid orAndNotOr :=
  orAndNotOrPattern_valid false false

public def orAndNotCommutedOr : Pattern OpCode := orAndNotOrPattern true false

public theorem orAndNotCommutedOr_valid : Pattern.Valid orAndNotCommutedOr :=
  orAndNotOrPattern_valid true false

public def orAndNotOrConstantLeft : Pattern OpCode := orAndNotOrPattern false true
public theorem orAndNotOrConstantLeft_valid : Pattern.Valid orAndNotOrConstantLeft :=
  orAndNotOrPattern_valid false true

public def orAndNotCommutedOrConstantLeft : Pattern OpCode :=
  orAndNotOrPattern true true
public theorem orAndNotCommutedOrConstantLeft_valid :
    Pattern.Valid orAndNotCommutedOrConstantLeft :=
  orAndNotOrPattern_valid true true

end Veir.Passes.InstCombineLLVM.OrAndNotOr

#print axioms Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotOr_valid
#print axioms Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotCommutedOr_valid
#print axioms Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotOrConstantLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotCommutedOrConstantLeft_valid
