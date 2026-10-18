module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.UsubSatTruncToICmp

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval]
theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def isOneIntegerConstant
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match input.1.cast? IntegerType, (asLLVMConstantProperties input.2).value with
  | some intType, .integer attr => BitVec.ofInt intType.bitwidth attr.value == 1
  | _, _ => false

private def zeroConstantProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 0 intType))

/-- InstCombineCasts.cpp:1170-1173 for arbitrary scalar integer widths:
    `trunc (usub.sat 1, x) to i1` becomes `x == 0`. -/
public def usubSatOneTruncToICmpEqZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let wideTy ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let one ← MatchProg.operation (.llvm .mlir__constant) #[] #[wideTy]
        isIntegralConstant
      MatchProg.matchNative (wideTy, one.properties) isOneIntegerConstant
      let x ← MatchProg.value wideTy
      let saturated ← MatchProg.operation (.llvm .intr__usub__sat)
        #[one.res[0]!, x] #[wideTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[saturated.res[0]!] #[boolTy]
        (fun _ => true)
      return (wideTy, boolTy, x))
    (fun (wideTy, boolTy, x) => do
      let zeroProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        wideTy zeroConstantProperty
      let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[wideTy] zeroProps
      let cmpProps ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .eq)
      CreateProg.operation (.llvm .icmp) #[x, zero.res[0]!] #[boolTy] cmpProps)
    (fun result => result.res[0]!)

public theorem usubSatOneTruncToICmpEqZero_valid : Pattern.Valid usubSatOneTruncToICmpEqZero := by
  simp only [usubSatOneTruncToICmpEqZero]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [properties_of, guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ boolType ⟨boolW, boolSignedness⟩ hBool hBoolW
  subst boolType; change boolW = 1 at hBoolW; subst boolW
  rintro constantProps one hIntegral hInterpOne
  generalize hTyped : asLLVMConstantProperties constantProps = typedProps
  cases typedProps with
  | mk constantValue => cases constantValue with
    | float _ | dense _ | string _ => simp [isIntegralConstant, hTyped] at hIntegral
    | integer oneAttr =>
      have hInterpTyped : InterpretsTo (.llvm .mlir__constant)
          (asLLVMConstantProperties constantProps)
          #[IntegerType.mk w signedness] #[] #[one] := hInterpOne
      rw [hTyped] at hInterpTyped
      obtain rfl := (constant_iff _ oneAttr _).mp hInterpTyped
      rintro x hX
      obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
      rintro _ saturated hSaturated
      obtain rfl := (usub_sat_iff w (.val (BitVec.ofInt w oneAttr.value)) x saturated).mp
        hSaturated
      rintro truncProps source hSource hOne
      obtain ⟨h1w, rfl⟩ := (trunc_iff w 1 truncProps _ source).mp hSource
      have hOneValue : BitVec.ofInt w oneAttr.value = (1 : BitVec w) := by
        exact beq_iff_eq.mp (by
          simpa [isOneIntegerConstant, hTyped, IsTypeAttr.cast?_of] using hOne)
      simp [zeroConstantProperty, IsTypeAttr.cast?_of]
      refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int w (.val z))
          (ofInt_normalizeValue { bitwidth := w, signedness := signedness } 0).symm
      refine ⟨.int 1 (LLVM.Int.icmp x (.val (BitVec.ofInt w 0)) .eq), ?_, ?_⟩
      · exact (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl
      refine ⟨rfl, ?_⟩
      have hConst : BitVec.ofInt w oneAttr.value = BitVec.ofInt w 1 := by
        calc
          BitVec.ofInt w oneAttr.value = (1 : BitVec w) := hOneValue
          _ = BitVec.ofInt w 1 := rfl
      rw [hConst]
      simpa only [LLVM.Int.cast_self] using
        trunc_usub_sat_one_refines_icmp_eq_zero h1w x truncProps.nsw truncProps.nuw

end Veir.Passes.InstCombineLLVM.UsubSatTruncToICmp

#print axioms Veir.Passes.InstCombineLLVM.UsubSatTruncToICmp.usubSatOneTruncToICmpEqZero_valid
