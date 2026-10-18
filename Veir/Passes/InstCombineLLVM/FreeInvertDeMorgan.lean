module

public import Veir.Passes.InstCombineLLVM.CoreInversionSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def invertOrPattern (notXLeft notYLeft outerNotLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let notX ← if notXLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, x] #[ty] (fun _ => true)
      else MatchProg.operation (.llvm .xor) #[x, minusOne] #[ty] (fun _ => true)
      let notY ← if notYLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, y] #[ty] (fun _ => true)
      else MatchProg.operation (.llvm .xor) #[y, minusOne] #[ty] (fun _ => true)
      let both ← MatchProg.operation (.llvm .or) #[notX.res[0]!, notY.res[0]!]
        #[ty] (fun _ => true)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[minusOne, both.res[0]!] #[ty] (fun _ => true)
      else MatchProg.root (.llvm .xor) #[both.res[0]!, minusOne] #[ty] (fun _ => true)
      return (ty, x, y))
    (fun (ty, x, y) => do
      let props ← CreateProg.property (.llvm .and) ()
      CreateProg.operation (.llvm .and) #[x, y] #[ty] props)
    (fun result => result.res[0]!)

private def invertAndPattern (notXLeft notYLeft outerNotLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let notX ← if notXLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, x] #[ty] (fun _ => true)
      else MatchProg.operation (.llvm .xor) #[x, minusOne] #[ty] (fun _ => true)
      let notY ← if notYLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, y] #[ty] (fun _ => true)
      else MatchProg.operation (.llvm .xor) #[y, minusOne] #[ty] (fun _ => true)
      let both ← MatchProg.operation (.llvm .and) #[notX.res[0]!, notY.res[0]!]
        #[ty] (fun _ => true)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[minusOne, both.res[0]!] #[ty] (fun _ => true)
      else MatchProg.root (.llvm .xor) #[both.res[0]!, minusOne] #[ty] (fun _ => true)
      return (ty, x, y))
    (fun (ty, x, y) => do
      let props ← CreateProg.property (.llvm .or) default
      CreateProg.operation (.llvm .or) #[x, y] #[ty] props)
    (fun result => result.res[0]!)

macro "proveDeMorganStructure" : tactic =>
  `(tactic|
    (constructor
     · provePuddleSupported
     · open scoped PuddleCbv in cbv
     · open scoped PuddleCbv in cbv <;> simp [properties_of, guard_eq_cond_punit,
         MatchProg.collectBindings, MatchProg.collectDeclBindings,
         MatchProg.rootResults?, HandleContext.forbid, HandleContext.forbidMany,
         HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
         HandleContext.requireMany, HandleContext.insertFresh,
         HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
         MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
         CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]))

set_option maxHeartbeats 1500000 in
private theorem invertOrPattern_valid (notXLeft notYLeft outerNotLeft : Bool) :
    Pattern.Valid (invertOrPattern notXLeft notYLeft outerNotLeft) := by
  cases notXLeft <;> cases notYLeft <;> cases outerNotLeft <;>
    simp only [invertOrPattern, matchIntConstantNormalized, Bool.false_eq_true,
      ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    proveDeMorganStructure
    simpScalarPropertyPuddleSemantics
    rintro ⟨w, signedness⟩ x y
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ notX hNotX
      obtain rfl := (xor_iff _ _ _ _).mp hNotX
      rintro ⟨⟩ notY hNotY
      obtain rfl := (xor_iff _ _ _ _).mp hNotY
      rintro bothProps both hBoth
      obtain rfl := (or_iff _ _ _ _ _).mp hBoth
      rintro ⟨⟩ source hSource hMinusOne
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      have hBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hBits]
      refine ⟨.int w (LLVM.Int.and x y), (and_iff _ _ _ _).mpr rfl, rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
        not_or_not_not_refines_and w x y bothProps.disjoint

set_option maxHeartbeats 1500000 in
private theorem invertAndPattern_valid (notXLeft notYLeft outerNotLeft : Bool) :
    Pattern.Valid (invertAndPattern notXLeft notYLeft outerNotLeft) := by
  cases notXLeft <;> cases notYLeft <;> cases outerNotLeft <;>
    simp only [invertAndPattern, matchIntConstantNormalized, Bool.false_eq_true,
      ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    proveDeMorganStructure
    simpScalarPropertyPuddleSemantics
    rintro ⟨w, signedness⟩ x y
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ notX hNotX
      obtain rfl := (xor_iff _ _ _ _).mp hNotX
      rintro ⟨⟩ notY hNotY
      obtain rfl := (xor_iff _ _ _ _).mp hNotY
      rintro ⟨⟩ both hBoth
      obtain rfl := (and_iff _ _ _ _).mp hBoth
      rintro ⟨⟩ source hSource hMinusOne
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      have hBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hBits]
      refine ⟨.int w (LLVM.Int.or x y false), (or_iff _ _ _ _ _).mpr rfl, rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
        not_and_not_not_refines_or w x y

public def invertOr : Pattern OpCode := invertOrPattern false false false
public theorem invertOr_valid : Pattern.Valid invertOr := invertOrPattern_valid false false false
public def invertOrXLeft : Pattern OpCode := invertOrPattern true false false
public theorem invertOrXLeft_valid : Pattern.Valid invertOrXLeft := invertOrPattern_valid true false false
public def invertOrYLeft : Pattern OpCode := invertOrPattern false true false
public theorem invertOrYLeft_valid : Pattern.Valid invertOrYLeft := invertOrPattern_valid false true false
public def invertOrBothInnerLeft : Pattern OpCode := invertOrPattern true true false
public theorem invertOrBothInnerLeft_valid : Pattern.Valid invertOrBothInnerLeft := invertOrPattern_valid true true false
public def invertOrOuterLeft : Pattern OpCode := invertOrPattern false false true
public theorem invertOrOuterLeft_valid : Pattern.Valid invertOrOuterLeft := invertOrPattern_valid false false true
public def invertOrXOuterLeft : Pattern OpCode := invertOrPattern true false true
public theorem invertOrXOuterLeft_valid : Pattern.Valid invertOrXOuterLeft := invertOrPattern_valid true false true
public def invertOrYOuterLeft : Pattern OpCode := invertOrPattern false true true
public theorem invertOrYOuterLeft_valid : Pattern.Valid invertOrYOuterLeft := invertOrPattern_valid false true true
public def invertOrAllLeft : Pattern OpCode := invertOrPattern true true true
public theorem invertOrAllLeft_valid : Pattern.Valid invertOrAllLeft := invertOrPattern_valid true true true

public def invertAnd : Pattern OpCode := invertAndPattern false false false
public theorem invertAnd_valid : Pattern.Valid invertAnd := invertAndPattern_valid false false false
public def invertAndXLeft : Pattern OpCode := invertAndPattern true false false
public theorem invertAndXLeft_valid : Pattern.Valid invertAndXLeft := invertAndPattern_valid true false false
public def invertAndYLeft : Pattern OpCode := invertAndPattern false true false
public theorem invertAndYLeft_valid : Pattern.Valid invertAndYLeft := invertAndPattern_valid false true false
public def invertAndBothInnerLeft : Pattern OpCode := invertAndPattern true true false
public theorem invertAndBothInnerLeft_valid : Pattern.Valid invertAndBothInnerLeft := invertAndPattern_valid true true false
public def invertAndOuterLeft : Pattern OpCode := invertAndPattern false false true
public theorem invertAndOuterLeft_valid : Pattern.Valid invertAndOuterLeft := invertAndPattern_valid false false true
public def invertAndXOuterLeft : Pattern OpCode := invertAndPattern true false true
public theorem invertAndXOuterLeft_valid : Pattern.Valid invertAndXOuterLeft := invertAndPattern_valid true false true
public def invertAndYOuterLeft : Pattern OpCode := invertAndPattern false true true
public theorem invertAndYOuterLeft_valid : Pattern.Valid invertAndYOuterLeft := invertAndPattern_valid false true true
public def invertAndAllLeft : Pattern OpCode := invertAndPattern true true true
public theorem invertAndAllLeft_valid : Pattern.Valid invertAndAllLeft := invertAndPattern_valid true true true

end Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan
