module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcLt

open Veir Veir.Data Veir.Puddle Veir.Data.PBV Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def widthOrder (input : TypeAttr × TypeAttr × TypeAttr) : Bool :=
  match input.1.cast? IntegerType, input.2.1.cast? IntegerType,
      input.2.2.cast? IntegerType with
  | some src, some mid, some dst => mid.bitwidth < src.bitwidth && src.bitwidth < dst.bitwidth
  | _, _, _ => false

private def maskProperty (input : TypeAttr × TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some src := input.1.cast? IntegerType | none
  let some mid := input.2.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer
    (IntegerAttr.ofInt (Int.ofNat (2 ^ mid.bitwidth - 1)) src))

/-- Arbitrary-width scalar instance of InstCombineCasts.cpp:1697-1717. -/
public def zextTruncLowMaskSrcLt : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let midTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative (srcTy, midTy, dstTy) widthOrder
      let x ← MatchProg.value srcTy
      let trunc ← MatchProg.operation (.llvm .trunc) #[x] #[midTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .zext) #[trunc.res[0]!] #[dstTy] (fun _ => true)
      return (srcTy, midTy, dstTy, x))
    (fun (srcTy, midTy, dstTy, x) => do
      let maskProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        (srcTy, midTy) maskProperty
      let mask ← CreateProg.operation (.llvm .mlir__constant) #[] #[srcTy] maskProps
      let andProps ← CreateProg.property (.llvm .and) ()
      let andOp ← CreateProg.operation (.llvm .and) #[x, mask.res[0]!] #[srcTy] andProps
      let zextProps ← CreateProg.property (.llvm .zext) { nneg := false }
      CreateProg.operation (.llvm .zext) #[andOp.res[0]!] #[dstTy] zextProps)
    (fun result => result.res[0]!)

public theorem zextTruncLowMaskSrcLt_valid : Pattern.Valid zextTruncLowMaskSrcLt := by
  simp only [zextTruncLowMaskSrcLt]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨midW, midSignedness⟩ ⟨dstW, dstSignedness⟩
  rintro x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro truncProps truncated hTruncated
  obtain ⟨hMidSrc, rfl⟩ := (trunc_iff srcW midW truncProps x truncated).mp hTruncated
  rintro zextProps source hSource
  obtain ⟨hMidDst, rfl⟩ := (zext_iff midW dstW zextProps _ source).mp hSource
  rintro hWidths
  simp only [widthOrder, IsTypeAttr.cast?_of, Bool.and_eq_true,
    decide_eq_true_eq] at hWidths
  obtain ⟨hMidSrc', hSrcDst⟩ := hWidths
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
  refine ⟨.int dstW (LLVM.Int.zext
    (LLVM.Int.and x (.val (BitVec.ofInt srcW (Int.ofNat (2 ^ midW - 1)))))
      dstW false hSrcDst), ?_, ?_⟩
  · exact (zext_iff srcW dstW { nneg := false } _ _).mpr ⟨hSrcDst, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa [Veir.Data.PBV.maskOfWidth] using
    zext_trunc_lowmask_src_lt hMidSrc hSrcDst x
      truncProps.nsw truncProps.nuw zextProps.nneg

end Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcLt

#print axioms Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcLt.zextTruncLowMaskSrcLt_valid
