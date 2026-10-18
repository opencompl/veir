module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.OddShlTruncToICmp

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval]
theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def isOddIntegerConstant
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match input.1.cast? IntegerType, (asLLVMConstantProperties input.2).value with
  | some intType, .integer attr =>
      (BitVec.ofInt intType.bitwidth attr.value).getLsbD 0
  | _, _ => false

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def zeroConstantProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 0 intType))

/-- InstCombineCasts.cpp:1157-1162 for arbitrary scalar integer widths:
    `trunc (C << x) to i1` becomes `x == 0` when the constant C is odd. -/
public def oddShlTruncToICmpEqZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let wideTy ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[wideTy]
        isIntegralConstant
      MatchProg.matchNative (wideTy, c.properties) isOddIntegerConstant
      let x ← MatchProg.value wideTy
      let shifted ← MatchProg.operation (.llvm .shl) #[c.res[0]!, x] #[wideTy]
        (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[shifted.res[0]!] #[boolTy]
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

public theorem oddShlTruncToICmpEqZero_valid : Pattern.Valid oddShlTruncToICmpEqZero := by
  simp only [oddShlTruncToICmpEqZero]
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
  rintro constantProps c hIntegral hInterpC
  generalize hTyped : asLLVMConstantProperties constantProps = typedProps
  cases typedProps with
  | mk constantValue => cases constantValue with
    | float _ | dense _ | string _ => simp [isIntegralConstant, hTyped] at hIntegral
    | integer cAttr =>
      have hInterpTyped : InterpretsTo (.llvm .mlir__constant)
          (asLLVMConstantProperties constantProps)
          #[IntegerType.mk w signedness] #[] #[c] := hInterpC
      rw [hTyped] at hInterpTyped
      obtain rfl := (constant_iff _ cAttr _).mp hInterpTyped
      rintro x hX
      obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
      rintro shlProps shifted hShifted
      obtain rfl := (shl_iff _ shlProps _ _ _).mp hShifted
      rintro truncProps source hSource
      obtain ⟨h1w, rfl⟩ := (trunc_iff w 1 truncProps _ source).mp hSource
      rintro hOdd
      have hOddBit : (BitVec.ofInt w cAttr.value).getLsbD 0 = true := by
        simpa [isOddIntegerConstant, hTyped, IsTypeAttr.cast?_of] using hOdd
      simp [zeroConstantProperty, IsTypeAttr.cast?_of]
      refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int w (.val z))
          (ofInt_normalizeValue { bitwidth := w, signedness := signedness } 0).symm
      refine ⟨.int 1 (LLVM.Int.icmp x (.val (BitVec.ofInt w 0)) .eq), ?_, ?_⟩
      · exact (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl
      refine ⟨rfl, ?_⟩
      rw [show BitVec.ofInt w 0 = (0 : BitVec w) by rfl]
      simpa only [LLVM.Int.cast_self] using
        trunc_shl_odd_refines_icmp_eq_zero h1w (.val (BitVec.ofInt w cAttr.value)) x
          (by intro cv hcv; cases hcv; exact hOddBit)
          shlProps.nsw shlProps.nuw truncProps.nsw truncProps.nuw

end Veir.Passes.InstCombineLLVM.OddShlTruncToICmp

#print axioms Veir.Passes.InstCombineLLVM.OddShlTruncToICmp.oddShlTruncToICmpEqZero_valid
