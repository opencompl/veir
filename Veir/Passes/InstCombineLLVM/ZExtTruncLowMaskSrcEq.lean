module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcEq

open Veir Veir.Data Veir.Puddle Veir.Data.PBV Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl
@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t
private def widthLt (input : TypeAttr × TypeAttr) : Bool :=
  match input.1.cast? IntegerType, input.2.cast? IntegerType with
  | some wide, some narrow => narrow.bitwidth < wide.bitwidth
  | _, _ => false

private def maskProperty (input : TypeAttr × TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some wide := input.1.cast? IntegerType | none
  let some narrow := input.2.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer
    (IntegerAttr.ofInt (Int.ofNat (2 ^ narrow.bitwidth - 1)) wide))

/-- Scalar arbitrary-width instance of InstCombineCasts.cpp:1719-1722. -/
public def zextTruncLowMaskSrcEq : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let midTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative (srcTy, midTy) widthLt
      let x ← MatchProg.value srcTy
      let trunc ← MatchProg.operation (.llvm .trunc) #[x] #[midTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .zext) #[trunc.res[0]!] #[srcTy] (fun _ => true)
      return (srcTy, midTy, x))
    (fun (srcTy, midTy, x) => do
      let maskProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        (srcTy, midTy) maskProperty
      let mask ← CreateProg.operation (.llvm .mlir__constant) #[] #[srcTy] maskProps
      let andProps ← CreateProg.property (.llvm .and) ()
      CreateProg.operation (.llvm .and) #[x, mask.res[0]!] #[srcTy] andProps)
    (fun result => result.res[0]!)

public theorem zextTruncLowMaskSrcEq_valid : Pattern.Valid zextTruncLowMaskSrcEq := by
  simp only [zextTruncLowMaskSrcEq]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨srcW, srcSignedness⟩ ⟨midW, midSignedness⟩
  rintro x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro truncProps truncated hTruncated
  obtain ⟨hmidSrc, rfl⟩ := (trunc_iff srcW midW truncProps x truncated).mp hTruncated
  rintro zextProps source hSource
  obtain ⟨hmidSrc', rfl⟩ := (zext_iff midW srcW zextProps _ source).mp hSource
  rintro hWidths
  simp only [widthLt, IsTypeAttr.cast?_of] at hWidths
  have hlt : midW < srcW := of_decide_eq_true hWidths
  simp [maskProperty, IsTypeAttr.cast?_of]
  refine ⟨.int srcW (.val (BitVec.ofInt srcW (Int.ofNat (2 ^ midW - 1)))), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg
      (fun z => RuntimeValue.int srcW (.val z))
      (ofInt_normalizeValue { bitwidth := srcW, signedness := srcSignedness }
        (Int.ofNat (2 ^ midW - 1))).symm
  refine ⟨.int srcW (LLVM.Int.and x
      (.val (BitVec.ofInt srcW (Int.ofNat (2 ^ midW - 1))))),
    (and_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa [Veir.Data.PBV.maskOfWidth] using
    zext_trunc_lowmask_src_eq hlt x truncProps.nsw truncProps.nuw zextProps.nneg

end Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcEq

#print axioms Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcEq.zextTruncLowMaskSrcEq_valid
