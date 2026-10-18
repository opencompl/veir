module

public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NegateNot

open Veir
open Veir.Data
open Veir.Puddle
open Veir.Passes.InstCombineLLVM

@[local cbv_eval]
theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def negateNotPattern (notConstantLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let notX ← if notConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, x] #[ty]
      else
        MatchProg.operation (.llvm .xor) #[x, minusOne] #[ty]
      let zero ← matchIntConstant ty 0
      let _ ← MatchProg.root (.llvm .sub) #[zero, notX.res[0]!] #[ty] (fun _ => true)
      return (ty, x))
    (fun (ty, x) => do
      let oneProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty fun type => do
          let some intType := type.cast? IntegerType | none
          return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 1 intType))
      let one ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] oneProps
      let addProps ← CreateProg.property (.llvm .add) default
      let result ← CreateProg.operation (.llvm .add) #[x, one.res[0]!] #[ty] addProps
      return result)
    (fun result => result.res[0]!)

private theorem negateNotPattern_valid (notConstantLeft : Bool) :
    Pattern.Valid (negateNotPattern notConstantLeft) := by
  cases notConstantLeft <;> simp only [negateNotPattern, matchIntConstant,
    matchIntConstantNormalized,
    Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    proveScalarPuddleStructure
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index,
      forall_eq_apply_imp_iff]
    rintro ⟨w, signedness⟩ x
    rintro ⟨minusOneValue⟩ minusOne hinterpMinusOne
    cases minusOneValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hinterpMinusOne
      rintro _ notX hinterpNotX
      obtain rfl := (xor_iff _ _ _ _).mp hinterpNotX
      rintro ⟨zeroValue⟩ zero hZero hinterpZero
      cases zeroValue with
      | float _ | dense _ | string _ => simp at hZero
      | integer zeroAttr =>
        have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
        obtain rfl := (constant_iff _ zeroAttr _).mp hinterpZero
        rintro negProps source hinterpSource
        obtain rfl := (sub_iff _ _ _ _ _).mp hinterpSource
        rintro hMinusOne
        have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
          simpa [isNormalizedIntConstant, asLLVMConstantProperties,
            IsTypeAttr.cast?_of] using hMinusOne
        rw [hMinusOneBits, hZeroValue]
        simp only [IsTypeAttr.cast?_of]
        refine ⟨.int w (.val (BitVec.ofInt w 1)), ?_, ?_⟩
        · apply (constant_iff _ _ _).mpr
          simpa [IntegerAttr.ofInt] using congrArg
            (fun z => RuntimeValue.int w (.val z))
            (ofInt_normalizeValue { bitwidth := w, signedness := signedness } 1).symm
        refine ⟨.int w (LLVM.Int.add x (.val (BitVec.ofInt w 1))), ?_, ?_⟩
        · exact (add_iff _ _ _ _ _).mpr rfl
        first
        | change ∃ h : w = w,
            (LLVM.Int.sub (.val (BitVec.ofInt w 0))
              (LLVM.Int.xor x (.val (BitVec.ofInt w (-1))))
              negProps.nsw negProps.nuw).cast h ⊒
              LLVM.Int.add x (.val (BitVec.ofInt w 1))
        | change ∃ h : w = w,
            (LLVM.Int.sub (.val (BitVec.ofInt w 0))
              (LLVM.Int.xor (.val (BitVec.ofInt w (-1))) x)
              negProps.nsw negProps.nuw).cast h ⊒
              LLVM.Int.add x (.val (BitVec.ofInt w 1))
        refine ⟨rfl, ?_⟩
        simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
          (neg_not_refines w x negProps.nsw negProps.nuw)

/-- Scalar specialization of InstCombineNegator.cpp:160-165: `-(~x) -> x + 1`. -/
public def negateNot : Pattern OpCode := negateNotPattern false
public theorem negateNot_valid : Pattern.Valid negateNot := negateNotPattern_valid false

/-- LLVM `m_Not` variant with the all-ones constant as the XOR left operand. -/
public def negateNotConstantLeft : Pattern OpCode := negateNotPattern true
public theorem negateNotConstantLeft_valid : Pattern.Valid negateNotConstantLeft :=
  negateNotPattern_valid true

end Veir.Passes.InstCombineLLVM.NegateNot
