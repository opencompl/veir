module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.AndComplementaryOrs

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def andComplementaryOrsPattern
    (leftCommuted rightCommuted notBConstantLeft notAConstantLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let notB ← if notBConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, b] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[b, minusOne] #[ty] (fun _ => true)
      let left ← if leftCommuted then
        MatchProg.operation (.llvm .or) #[notB.res[0]!, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[a, notB.res[0]!] #[ty] (fun _ => true)
      let notA ← if notAConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[a, minusOne] #[ty] (fun _ => true)
      let right ← if rightCommuted then
        MatchProg.operation (.llvm .or) #[b, notA.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[notA.res[0]!, b] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .and) #[left.res[0]!, right.res[0]!] #[ty]
        (fun _ => true)
      return (ty, a, b, minusOne))
    (fun (ty, a, b, minusOne) => do
      let xp ← CreateProg.property (.llvm .xor) ()
      let xor ← CreateProg.operation (.llvm .xor) #[a, b] #[ty] xp
      let np ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[xor.res[0]!, minusOne] #[ty] np)
    (fun result => result.res[0]!)

set_option maxHeartbeats 2000000 in
private theorem andComplementaryOrsPattern_valid
    (leftCommuted rightCommuted notBConstantLeft notAConstantLeft : Bool) :
    Pattern.Valid (andComplementaryOrsPattern leftCommuted rightCommuted notBConstantLeft notAConstantLeft) := by
  cases leftCommuted <;> cases rightCommuted <;> cases notBConstantLeft <;>
    cases notAConstantLeft <;>
    simp only [andComplementaryOrsPattern, matchIntConstantNormalized, Bool.false_eq_true,
      ite_false, ite_true] <;> unfoldPuddleBuilder
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
      rintro ⟨⟩ notB hNotB
      obtain rfl := (xor_iff _ _ _ _).mp hNotB
      rintro leftProps left hLeft
      obtain rfl := (or_iff _ _ _ _ _).mp hLeft
      rintro ⟨⟩ notA hNotA
      obtain rfl := (xor_iff _ _ _ _).mp hNotA
      rintro rightProps right hRight
      obtain rfl := (or_iff _ _ _ _ _).mp hRight
      rintro ⟨⟩ source hSource
      obtain rfl := (and_iff _ _ _ _).mp hSource
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
        (complementary_ors_and_refines_not_xor w a b
          leftProps.disjoint rightProps.disjoint)

/- Scalar semantic specialization of InstCombineAndOrXor.cpp:1962-1965.
   Puddle currently omits the source's profitability-only one-use guard. -/
public def andComplementaryOrs : Pattern OpCode :=
  andComplementaryOrsPattern false false false false

public theorem andComplementaryOrs_valid : Pattern.Valid andComplementaryOrs :=
  andComplementaryOrsPattern_valid false false false false

public def andLeftCommutedComplementaryOrs : Pattern OpCode :=
  andComplementaryOrsPattern true false false false

public theorem andLeftCommutedComplementaryOrs_valid :
    Pattern.Valid andLeftCommutedComplementaryOrs :=
  andComplementaryOrsPattern_valid true false false false

public def andRightCommutedComplementaryOrs : Pattern OpCode :=
  andComplementaryOrsPattern false true false false

public theorem andRightCommutedComplementaryOrs_valid :
    Pattern.Valid andRightCommutedComplementaryOrs :=
  andComplementaryOrsPattern_valid false true false false

public def andCommutedComplementaryOrs : Pattern OpCode :=
  andComplementaryOrsPattern true true false false

public theorem andCommutedComplementaryOrs_valid :
    Pattern.Valid andCommutedComplementaryOrs :=
  andComplementaryOrsPattern_valid true true false false

public def andComplementaryOrsNotBLeft : Pattern OpCode :=
  andComplementaryOrsPattern false false true false
public theorem andComplementaryOrsNotBLeft_valid : Pattern.Valid andComplementaryOrsNotBLeft :=
  andComplementaryOrsPattern_valid false false true false

public def andComplementaryOrsNotALeft : Pattern OpCode :=
  andComplementaryOrsPattern false false false true
public theorem andComplementaryOrsNotALeft_valid : Pattern.Valid andComplementaryOrsNotALeft :=
  andComplementaryOrsPattern_valid false false false true

public def andComplementaryOrsBothNotLeft : Pattern OpCode :=
  andComplementaryOrsPattern false false true true
public theorem andComplementaryOrsBothNotLeft_valid : Pattern.Valid andComplementaryOrsBothNotLeft :=
  andComplementaryOrsPattern_valid false false true true

public def andLeftCommutedComplementaryOrsNotBLeft : Pattern OpCode :=
  andComplementaryOrsPattern true false true false
public theorem andLeftCommutedComplementaryOrsNotBLeft_valid : Pattern.Valid andLeftCommutedComplementaryOrsNotBLeft :=
  andComplementaryOrsPattern_valid true false true false

public def andLeftCommutedComplementaryOrsNotALeft : Pattern OpCode :=
  andComplementaryOrsPattern true false false true
public theorem andLeftCommutedComplementaryOrsNotALeft_valid : Pattern.Valid andLeftCommutedComplementaryOrsNotALeft :=
  andComplementaryOrsPattern_valid true false false true

public def andLeftCommutedComplementaryOrsBothNotLeft : Pattern OpCode :=
  andComplementaryOrsPattern true false true true
public theorem andLeftCommutedComplementaryOrsBothNotLeft_valid : Pattern.Valid andLeftCommutedComplementaryOrsBothNotLeft :=
  andComplementaryOrsPattern_valid true false true true

public def andRightCommutedComplementaryOrsNotBLeft : Pattern OpCode :=
  andComplementaryOrsPattern false true true false
public theorem andRightCommutedComplementaryOrsNotBLeft_valid : Pattern.Valid andRightCommutedComplementaryOrsNotBLeft :=
  andComplementaryOrsPattern_valid false true true false

public def andRightCommutedComplementaryOrsNotALeft : Pattern OpCode :=
  andComplementaryOrsPattern false true false true
public theorem andRightCommutedComplementaryOrsNotALeft_valid : Pattern.Valid andRightCommutedComplementaryOrsNotALeft :=
  andComplementaryOrsPattern_valid false true false true

public def andRightCommutedComplementaryOrsBothNotLeft : Pattern OpCode :=
  andComplementaryOrsPattern false true true true
public theorem andRightCommutedComplementaryOrsBothNotLeft_valid : Pattern.Valid andRightCommutedComplementaryOrsBothNotLeft :=
  andComplementaryOrsPattern_valid false true true true

public def andCommutedComplementaryOrsNotBLeft : Pattern OpCode :=
  andComplementaryOrsPattern true true true false
public theorem andCommutedComplementaryOrsNotBLeft_valid : Pattern.Valid andCommutedComplementaryOrsNotBLeft :=
  andComplementaryOrsPattern_valid true true true false

public def andCommutedComplementaryOrsNotALeft : Pattern OpCode :=
  andComplementaryOrsPattern true true false true
public theorem andCommutedComplementaryOrsNotALeft_valid : Pattern.Valid andCommutedComplementaryOrsNotALeft :=
  andComplementaryOrsPattern_valid true true false true

public def andCommutedComplementaryOrsBothNotLeft : Pattern OpCode :=
  andComplementaryOrsPattern true true true true
public theorem andCommutedComplementaryOrsBothNotLeft_valid : Pattern.Valid andCommutedComplementaryOrsBothNotLeft :=
  andComplementaryOrsPattern_valid true true true true

end Veir.Passes.InstCombineLLVM.AndComplementaryOrs

#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrs_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrs_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrs_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrs_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrsNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrsNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrsBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrsNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrsNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrsBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrsNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrsNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrsBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrsNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrsNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrsBothNotLeft_valid
