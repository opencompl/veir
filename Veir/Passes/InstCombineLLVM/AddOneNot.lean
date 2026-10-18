module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.AddOneNot

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

private def addOneNotPattern (alternate commuted notConstantLeft : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let one ← matchIntConstant ty 1
    let minusOne ← matchIntConstantNormalized ty (-1)
    let notB ← if notConstantLeft then
      MatchProg.operation (.llvm .xor) #[minusOne, b] #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .xor) #[b, minusOne] #[ty] (fun _ => true)
    let first ← if alternate then
      if commuted then
        MatchProg.operation (.llvm .add) #[a, notB.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .add) #[notB.res[0]!, a] #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .add) #[a, one] #[ty] (fun _ => true)
    let _ ← if alternate then
      MatchProg.root (.llvm .add) #[first.res[0]!, one] #[ty] (fun _ => true)
    else
      if commuted then
        MatchProg.root (.llvm .add) #[notB.res[0]!, first.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .add) #[first.res[0]!, notB.res[0]!] #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let sp ← CreateProg.property (.llvm .sub) default
    CreateProg.operation (.llvm .sub) #[a, b] #[ty] sp)
  (fun result => result.res[0]!)

set_option maxHeartbeats 800000 in
private theorem addOneNotPattern_valid (alternate commuted notConstantLeft : Bool) :
    Pattern.Valid (addOneNotPattern alternate commuted notConstantLeft) := by
  cases alternate <;> cases commuted <;> cases notConstantLeft <;>
    simp only [addOneNotPattern, matchIntConstant, matchIntConstantNormalized,
      Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    proveScalarPuddleStructure
    simpScalarPuddleSemantics
    rintro ⟨w, signedness⟩ a b
    rintro ⟨oneValue⟩ one hOne hInterpOne
    cases oneValue with
    | float _ | dense _ | string _ => simp at hOne
    | integer oneAttr =>
      have hOneValue : oneAttr.value = 1 := of_decide_eq_true hOne
      obtain rfl := (constant_iff _ oneAttr _).mp hInterpOne
      rintro ⟨minusOneValue⟩ minusOne hInterpMinusOne
      cases minusOneValue with
      | float _ | dense _ | string _ =>
        rintro _ _ _ _ _ _ _ _ _ hMinusOne
        simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
      | integer minusOneAttr =>
        obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
        rintro ⟨⟩ notB hNotB
        obtain rfl := (xor_iff _ _ _ _).mp hNotB
        rintro firstProps first hFirst
        obtain rfl := (add_iff _ _ _ _ _).mp hFirst
        rintro outerProps source hSource
        obtain rfl := (add_iff _ _ _ _ _).mp hSource
        rintro hMinusOne
        have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
          simpa [isNormalizedIntConstant, asLLVMConstantProperties,
            IsTypeAttr.cast?_of] using hMinusOne
        rw [hOneValue, hMinusOneBits]
        refine ⟨.int w (LLVM.Int.sub a b), (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
        refine ⟨rfl, ?_⟩
        first
        | simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
            (add_one_not_refines_sub w a b firstProps.nsw firstProps.nuw
              outerProps.nsw outerProps.nuw)
        | simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
            (not_add_one_refines_sub w a b firstProps.nsw firstProps.nuw
              outerProps.nsw outerProps.nuw)
        | simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
            (not_plus_add_one_refines_sub w a b firstProps.nsw firstProps.nuw
              outerProps.nsw outerProps.nuw)
        | simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
            (add_not_one_refines_sub w a b firstProps.nsw firstProps.nuw
              outerProps.nsw outerProps.nuw)

/-- First source graph at InstCombineAddSub.cpp:1691-1698. -/
public def addOneNot : Pattern OpCode := addOneNotPattern false false false
public theorem addOneNot_valid : Pattern.Valid addOneNot := addOneNotPattern_valid false false false

/-- Outer-commuted `~B + (A + 1)` source matcher arrangement. -/
public def notAddOne : Pattern OpCode := addOneNotPattern false true false
public theorem notAddOne_valid : Pattern.Valid notAddOne := addOneNotPattern_valid false true false

/-- Alternate source graph `add (add (~B), A), 1`. -/
public def addNotOne : Pattern OpCode := addOneNotPattern true false false
public theorem addNotOne_valid : Pattern.Valid addNotOne := addOneNotPattern_valid true false false

/-- Inner-commuted `(A + ~B) + 1` source matcher arrangement. -/
public def addCommutedNotOne : Pattern OpCode := addOneNotPattern true true false
public theorem addCommutedNotOne_valid : Pattern.Valid addCommutedNotOne :=
  addOneNotPattern_valid true true false

public def addOneNotConstantLeft : Pattern OpCode := addOneNotPattern false false true
public theorem addOneNotConstantLeft_valid : Pattern.Valid addOneNotConstantLeft :=
  addOneNotPattern_valid false false true

public def notAddOneConstantLeft : Pattern OpCode := addOneNotPattern false true true
public theorem notAddOneConstantLeft_valid : Pattern.Valid notAddOneConstantLeft :=
  addOneNotPattern_valid false true true

public def addNotOneConstantLeft : Pattern OpCode := addOneNotPattern true false true
public theorem addNotOneConstantLeft_valid : Pattern.Valid addNotOneConstantLeft :=
  addOneNotPattern_valid true false true

public def addCommutedNotOneConstantLeft : Pattern OpCode := addOneNotPattern true true true
public theorem addCommutedNotOneConstantLeft_valid :
    Pattern.Valid addCommutedNotOneConstantLeft :=
  addOneNotPattern_valid true true true

end Veir.Passes.InstCombineLLVM.AddOneNot
