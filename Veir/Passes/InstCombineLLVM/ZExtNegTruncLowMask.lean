module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.ZExtNegTruncLowMask

open Veir Veir.Data Veir.Puddle Veir.Data.PBV Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl
@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def intProperty (value : Int) (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt value intType))

private def maskProperty (input : TypeAttr × TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some wide := input.1.cast? IntegerType | none
  let some narrow := input.2.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer
    (IntegerAttr.ofInt (Int.ofNat (2 ^ narrow.bitwidth - 1)) wide))

/-- Arbitrary-width scalar instance of InstCombineCasts.cpp:1747-1753. -/
public def zextNegTruncLowMask : Pattern OpCode :=
  Pattern.Builder
    (do
      let wideTy ← MatchProg.type (Attr := IntegerType)
      let narrowTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value wideTy
      let trunc ← MatchProg.operation (.llvm .trunc) #[x] #[narrowTy] (fun _ => true)
      let zero ← matchIntConstant narrowTy 0
      let neg ← MatchProg.operation (.llvm .sub) #[zero, trunc.res[0]!] #[narrowTy]
        (fun _ => true)
      let _ ← MatchProg.root (.llvm .zext) #[neg.res[0]!] #[wideTy] (fun _ => true)
      return (wideTy, narrowTy, x))
    (fun (wideTy, narrowTy, x) => do
      let zeroProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) wideTy (intProperty 0)
      let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[wideTy] zeroProps
      let sp ← CreateProg.property (.llvm .sub) default
      let neg ← CreateProg.operation (.llvm .sub) #[zero.res[0]!, x] #[wideTy] sp
      let maskProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        (wideTy, narrowTy) maskProperty
      let mask ← CreateProg.operation (.llvm .mlir__constant) #[] #[wideTy] maskProps
      let ap ← CreateProg.property (.llvm .and) ()
      CreateProg.operation (.llvm .and) #[neg.res[0]!, mask.res[0]!] #[wideTy] ap)
    (fun result => result.res[0]!)

public theorem zextNegTruncLowMask_valid : Pattern.Valid zextNegTruncLowMask := by
  simp only [zextNegTruncLowMask, matchIntConstant]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.requireBindings, MetadataTuple.Shape.insertFreshBindings,
      IsMetadataTuple.shape_type, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨wideW, wideSignedness⟩ ⟨narrowW, narrowSignedness⟩
  rintro x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro truncProps truncated hTruncated
  obtain ⟨hNarrowWide, rfl⟩ :=
    (trunc_iff wideW narrowW truncProps x truncated).mp hTruncated
  rintro ⟨zeroValue⟩ zero hZero hInterpZero
  cases zeroValue with
  | float _ | dense _ | string _ => simp at hZero
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro subProps neg hNeg
    obtain rfl := (sub_iff _ _ _ _ _).mp hNeg
    rintro zextProps source hSource
    obtain ⟨hNarrowWide', rfl⟩ :=
      (zext_iff narrowW wideW zextProps _ source).mp hSource
    rw [hZeroValue]
    simp [intProperty, maskProperty, IsTypeAttr.cast?_of]
    refine ⟨.int wideW (.val (BitVec.ofInt wideW 0)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg
        (fun z => RuntimeValue.int wideW (.val z))
        (ofInt_normalizeValue { bitwidth := wideW, signedness := wideSignedness } 0).symm
    refine ⟨.int wideW (LLVM.Int.sub (.val (BitVec.ofInt wideW 0)) x),
      (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int wideW (.val
      (BitVec.ofInt wideW (Int.ofNat (2 ^ narrowW - 1)))), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg
        (fun z => RuntimeValue.int wideW (.val z))
        (ofInt_normalizeValue { bitwidth := wideW, signedness := wideSignedness }
          (Int.ofNat (2 ^ narrowW - 1))).symm
    refine ⟨.int wideW (LLVM.Int.and (LLVM.Int.sub (.val (BitVec.ofInt wideW 0)) x)
      (.val (BitVec.ofInt wideW (Int.ofNat (2 ^ narrowW - 1))))),
      (and_iff _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa [Veir.Data.PBV.maskOfWidth] using
      zext_neg_trunc_lowmask hNarrowWide x truncProps.nsw truncProps.nuw
        subProps.nsw subProps.nuw zextProps.nneg

end Veir.Passes.InstCombineLLVM.ZExtNegTruncLowMask

#print axioms Veir.Passes.InstCombineLLVM.ZExtNegTruncLowMask.zextNegTruncLowMask_valid
