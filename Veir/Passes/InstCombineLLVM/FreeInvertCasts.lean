module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.FreeInvertCasts

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def nonzeroIntegerWidth (input : TypeAttr) : Bool :=
  match input.cast? IntegerType with
  | some ty => 0 < ty.bitwidth
  | none => false

/-- Exact `A = ~X` specialization of the freely-inverted sext arm. -/
private def invertSExtPattern (innerNotLeft outerNotLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative srcTy nonzeroIntegerWidth
      let x ← MatchProg.value srcTy
      let srcMinusOne ← matchIntConstantNormalized srcTy (-1)
      let notX ← if innerNotLeft then
        MatchProg.operation (.llvm .xor) #[srcMinusOne, x] #[srcTy] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[x, srcMinusOne] #[srcTy] (fun _ => true)
      let extended ← MatchProg.operation (.llvm .sext) #[notX.res[0]!] #[dstTy]
        (fun _ => true)
      let dstMinusOne ← matchIntConstantNormalized dstTy (-1)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[dstMinusOne, extended.res[0]!] #[dstTy]
          (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[extended.res[0]!, dstMinusOne] #[dstTy]
          (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .sext) ()
      CreateProg.operation (.llvm .sext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem invertSExtPattern_valid (innerNotLeft outerNotLeft : Bool) :
    Pattern.Valid (invertSExtPattern innerNotLeft outerNotLeft) := by
  cases innerNotLeft <;> cases outerNotLeft <;>
    simp only [invertSExtPattern, matchIntConstantNormalized,
      Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [properties_of, guard_eq_cond_punit,
        MatchProg.collectBindings, MatchProg.collectDeclBindings,
        MatchDecl.collectBindings,
        MatchProg.rootResults?, HandleContext.forbid, HandleContext.forbidMany,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpScalarPropertyPuddleSemantics
    rintro ⟨srcW, srcSignedness⟩ ⟨dstW, dstSignedness⟩ x
    rintro ⟨srcConstantValue⟩ srcMinusOne hInterpSrcMinusOne
    cases srcConstantValue with
    | float _ | dense _ | string _ =>
      simp [isNormalizedIntConstant, asLLVMConstantProperties]
    | integer srcMinusOneAttr =>
      obtain rfl := (constant_iff _ srcMinusOneAttr _).mp hInterpSrcMinusOne
      rintro ⟨⟩ notX hNotX
      obtain rfl := (xor_iff _ _ _ _).mp hNotX
      rintro _ extended hExtended
      obtain ⟨hWiden, rfl⟩ := (sext_iff srcW dstW _ extended).mp hExtended
      rintro ⟨dstConstantValue⟩ dstMinusOne hInterpDstMinusOne
      cases dstConstantValue with
      | float _ | dense _ | string _ =>
        simp [isNormalizedIntConstant, asLLVMConstantProperties]
      | integer dstMinusOneAttr =>
        obtain rfl := (constant_iff _ dstMinusOneAttr _).mp hInterpDstMinusOne
        rintro ⟨⟩ source hSource
        obtain rfl := (xor_iff _ _ _ _).mp hSource
        rintro hNonzero hSrcMinusOne hDstMinusOne
        have hSrcBits : BitVec.ofInt srcW srcMinusOneAttr.value =
            BitVec.ofInt srcW (-1) := by
          simpa [nonzeroIntegerWidth, isNormalizedIntConstant,
            asLLVMConstantProperties, IsTypeAttr.cast?_of] using hSrcMinusOne
        have hDstBits : BitVec.ofInt dstW dstMinusOneAttr.value =
            BitVec.ofInt dstW (-1) := by
          simpa [nonzeroIntegerWidth, isNormalizedIntConstant,
            asLLVMConstantProperties, IsTypeAttr.cast?_of] using hDstMinusOne
        have hSrcPos : 0 < srcW := by
          change
            (match (TypeAttr.of IntegerType
                { bitwidth := srcW, signedness := srcSignedness }).cast? IntegerType with
              | some ty => 0 < ty.bitwidth
              | none => false) = true at hNonzero
          rw [IsTypeAttr.cast?_of] at hNonzero
          exact of_decide_eq_true hNonzero
        rw [hSrcBits, hDstBits]
        refine ⟨.int dstW (LLVM.Int.sext x dstW hWiden),
          (sext_iff srcW dstW x _).mpr ⟨hWiden, rfl⟩, ?_⟩
        refine ⟨rfl, ?_⟩
        simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
          invert_sext_not_refines hSrcPos hWiden x

public def invertSExt : Pattern OpCode := invertSExtPattern false false
public theorem invertSExt_valid : Pattern.Valid invertSExt :=
  invertSExtPattern_valid false false
public def invertSExtInnerLeft : Pattern OpCode := invertSExtPattern true false
public theorem invertSExtInnerLeft_valid : Pattern.Valid invertSExtInnerLeft :=
  invertSExtPattern_valid true false
public def invertSExtOuterLeft : Pattern OpCode := invertSExtPattern false true
public theorem invertSExtOuterLeft_valid : Pattern.Valid invertSExtOuterLeft :=
  invertSExtPattern_valid false true
public def invertSExtBothLeft : Pattern OpCode := invertSExtPattern true true
public theorem invertSExtBothLeft_valid : Pattern.Valid invertSExtBothLeft :=
  invertSExtPattern_valid true true


/-- Exact `A = ~X` specialization of the freely-inverted zext-nneg arm. -/
private def invertZExtNNegPattern (innerNotLeft outerNotLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative srcTy nonzeroIntegerWidth
      let x ← MatchProg.value srcTy
      let srcMinusOne ← matchIntConstantNormalized srcTy (-1)
      let notX ← if innerNotLeft then
        MatchProg.operation (.llvm .xor) #[srcMinusOne, x] #[srcTy] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[x, srcMinusOne] #[srcTy] (fun _ => true)
      let extended ← MatchProg.operation (.llvm .zext) #[notX.res[0]!] #[dstTy]
        (fun p => p.nneg = true)
      let dstMinusOne ← matchIntConstantNormalized dstTy (-1)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[dstMinusOne, extended.res[0]!] #[dstTy]
          (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[extended.res[0]!, dstMinusOne] #[dstTy]
          (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .sext) ()
      CreateProg.operation (.llvm .sext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem invertZExtNNegPattern_valid (innerNotLeft outerNotLeft : Bool) :
    Pattern.Valid (invertZExtNNegPattern innerNotLeft outerNotLeft) := by
  cases innerNotLeft <;> cases outerNotLeft <;>
    simp only [invertZExtNNegPattern, matchIntConstantNormalized,
      Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [properties_of, guard_eq_cond_punit,
        MatchProg.collectBindings, MatchProg.collectDeclBindings, MatchDecl.collectBindings,
        MatchProg.rootResults?, HandleContext.forbid, HandleContext.forbidMany,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpScalarPropertyPuddleSemantics
    rintro ⟨srcW, srcSignedness⟩ ⟨dstW, dstSignedness⟩ x
    rintro ⟨srcConstantValue⟩ srcMinusOne hInterpSrcMinusOne
    cases srcConstantValue with
    | float _ | dense _ | string _ =>
      simp [isNormalizedIntConstant, asLLVMConstantProperties]
    | integer srcMinusOneAttr =>
      obtain rfl := (constant_iff _ srcMinusOneAttr _).mp hInterpSrcMinusOne
      rintro ⟨⟩ notX hNotX
      obtain rfl := (xor_iff _ _ _ _).mp hNotX
      rintro zextProps extended hNNeg hExtended
      have hNNeg' : zextProps.nneg = true := of_decide_eq_true hNNeg
      obtain ⟨hWiden, rfl⟩ := (zext_iff srcW dstW zextProps _ extended).mp hExtended
      rintro ⟨dstConstantValue⟩ dstMinusOne hInterpDstMinusOne
      cases dstConstantValue with
      | float _ | dense _ | string _ =>
        simp [isNormalizedIntConstant, asLLVMConstantProperties]
      | integer dstMinusOneAttr =>
        obtain rfl := (constant_iff _ dstMinusOneAttr _).mp hInterpDstMinusOne
        rintro ⟨⟩ source hSource
        obtain rfl := (xor_iff _ _ _ _).mp hSource
        rintro hNonzero hSrcMinusOne hDstMinusOne
        have hSrcBits : BitVec.ofInt srcW srcMinusOneAttr.value =
            BitVec.ofInt srcW (-1) := by
          simpa [nonzeroIntegerWidth, isNormalizedIntConstant,
            asLLVMConstantProperties, IsTypeAttr.cast?_of] using hSrcMinusOne
        have hDstBits : BitVec.ofInt dstW dstMinusOneAttr.value =
            BitVec.ofInt dstW (-1) := by
          simpa [nonzeroIntegerWidth, isNormalizedIntConstant,
            asLLVMConstantProperties, IsTypeAttr.cast?_of] using hDstMinusOne
        have hSrcPos : 0 < srcW := by
          change
            (match (TypeAttr.of IntegerType
                { bitwidth := srcW, signedness := srcSignedness }).cast? IntegerType with
              | some ty => 0 < ty.bitwidth
              | none => false) = true at hNonzero
          rw [IsTypeAttr.cast?_of] at hNonzero
          exact of_decide_eq_true hNonzero
        rw [hSrcBits, hDstBits, hNNeg']
        refine ⟨.int dstW (LLVM.Int.sext x dstW hWiden),
          (sext_iff srcW dstW x _).mpr ⟨hWiden, rfl⟩, ?_⟩
        refine ⟨rfl, ?_⟩
        simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
          invert_zext_nneg_not_refines hSrcPos hWiden x

public def invertZExtNNeg : Pattern OpCode := invertZExtNNegPattern false false
public theorem invertZExtNNeg_valid : Pattern.Valid invertZExtNNeg :=
  invertZExtNNegPattern_valid false false
public def invertZExtNNegInnerLeft : Pattern OpCode := invertZExtNNegPattern true false
public theorem invertZExtNNegInnerLeft_valid : Pattern.Valid invertZExtNNegInnerLeft :=
  invertZExtNNegPattern_valid true false
public def invertZExtNNegOuterLeft : Pattern OpCode := invertZExtNNegPattern false true
public theorem invertZExtNNegOuterLeft_valid : Pattern.Valid invertZExtNNegOuterLeft :=
  invertZExtNNegPattern_valid false true
public def invertZExtNNegBothLeft : Pattern OpCode := invertZExtNNegPattern true true
public theorem invertZExtNNegBothLeft_valid : Pattern.Valid invertZExtNNegBothLeft :=
  invertZExtNNegPattern_valid true true

/-- Exact `A = ~X` specialization of the freely-inverted trunc arm. -/
private def invertTruncPattern (innerNotLeft outerNotLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative srcTy nonzeroIntegerWidth
      let x ← MatchProg.value srcTy
      let srcMinusOne ← matchIntConstantNormalized srcTy (-1)
      let notX ← if innerNotLeft then
        MatchProg.operation (.llvm .xor) #[srcMinusOne, x] #[srcTy] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[x, srcMinusOne] #[srcTy] (fun _ => true)
      let narrowed ← MatchProg.operation (.llvm .trunc) #[notX.res[0]!] #[dstTy]
        (fun _ => true)
      let dstMinusOne ← matchIntConstantNormalized dstTy (-1)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[dstMinusOne, narrowed.res[0]!] #[dstTy]
          (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[narrowed.res[0]!, dstMinusOne] #[dstTy]
          (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .trunc) default
      CreateProg.operation (.llvm .trunc) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem invertTruncPattern_valid (innerNotLeft outerNotLeft : Bool) :
    Pattern.Valid (invertTruncPattern innerNotLeft outerNotLeft) := by
  cases innerNotLeft <;> cases outerNotLeft <;>
    simp only [invertTruncPattern, matchIntConstantNormalized,
      Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [properties_of, guard_eq_cond_punit,
        MatchProg.collectBindings, MatchProg.collectDeclBindings, MatchDecl.collectBindings,
        MatchProg.rootResults?, HandleContext.forbid, HandleContext.forbidMany,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpScalarPropertyPuddleSemantics
    rintro ⟨srcW, srcSignedness⟩ ⟨dstW, dstSignedness⟩ x
    rintro ⟨srcConstantValue⟩ srcMinusOne hInterpSrcMinusOne
    cases srcConstantValue with
    | float _ | dense _ | string _ =>
      simp [isNormalizedIntConstant, asLLVMConstantProperties]
    | integer srcMinusOneAttr =>
      obtain rfl := (constant_iff _ srcMinusOneAttr _).mp hInterpSrcMinusOne
      rintro ⟨⟩ notX hNotX
      obtain rfl := (xor_iff _ _ _ _).mp hNotX
      rintro truncProps narrowed hNarrowed
      obtain ⟨hNarrow, rfl⟩ := (trunc_iff srcW dstW truncProps _ narrowed).mp hNarrowed
      rintro ⟨dstConstantValue⟩ dstMinusOne hInterpDstMinusOne
      cases dstConstantValue with
      | float _ | dense _ | string _ =>
        simp [isNormalizedIntConstant, asLLVMConstantProperties]
      | integer dstMinusOneAttr =>
        obtain rfl := (constant_iff _ dstMinusOneAttr _).mp hInterpDstMinusOne
        rintro ⟨⟩ source hSource
        obtain rfl := (xor_iff _ _ _ _).mp hSource
        rintro _hNonzero hSrcMinusOne hDstMinusOne
        have hSrcBits : BitVec.ofInt srcW srcMinusOneAttr.value =
            BitVec.ofInt srcW (-1) := by
          simpa [nonzeroIntegerWidth, isNormalizedIntConstant,
            asLLVMConstantProperties, IsTypeAttr.cast?_of] using hSrcMinusOne
        have hDstBits : BitVec.ofInt dstW dstMinusOneAttr.value =
            BitVec.ofInt dstW (-1) := by
          simpa [nonzeroIntegerWidth, isNormalizedIntConstant,
            asLLVMConstantProperties, IsTypeAttr.cast?_of] using hDstMinusOne
        rw [hSrcBits, hDstBits]
        refine ⟨.int dstW (LLVM.Int.trunc x dstW false false hNarrow),
          (trunc_iff srcW dstW default x _).mpr ⟨hNarrow, rfl⟩, ?_⟩
        refine ⟨rfl, ?_⟩
        simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
          invert_trunc_not_refines hNarrow x truncProps.nsw truncProps.nuw

public def invertTrunc : Pattern OpCode := invertTruncPattern false false
public theorem invertTrunc_valid : Pattern.Valid invertTrunc :=
  invertTruncPattern_valid false false
public def invertTruncInnerLeft : Pattern OpCode := invertTruncPattern true false
public theorem invertTruncInnerLeft_valid : Pattern.Valid invertTruncInnerLeft :=
  invertTruncPattern_valid true false
public def invertTruncOuterLeft : Pattern OpCode := invertTruncPattern false true
public theorem invertTruncOuterLeft_valid : Pattern.Valid invertTruncOuterLeft :=
  invertTruncPattern_valid false true
public def invertTruncBothLeft : Pattern OpCode := invertTruncPattern true true
public theorem invertTruncBothLeft_valid : Pattern.Valid invertTruncBothLeft :=
  invertTruncPattern_valid true true

end Veir.Passes.InstCombineLLVM.FreeInvertCasts

#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertSExt_valid
#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertSExtInnerLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertSExtOuterLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertSExtBothLeft_valid

#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertZExtNNeg_valid
#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertZExtNNegInnerLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertZExtNNegOuterLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertZExtNNegBothLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertTrunc_valid
#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertTruncInnerLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertTruncOuterLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertTruncBothLeft_valid
