module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.ZExtNNegI1
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl
@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def zeroProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 0 intType))

/-- Arbitrary scalar destination-width specialization of InstCombineCasts.cpp:1639-1644. -/
public def zextNNegI1ToZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let _ ← MatchProg.root (.llvm .zext) #[x] #[dstTy] (fun p => p.nneg = true)
      return dstTy)
    (fun dstTy => do
      let props ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) dstTy zeroProperty
      CreateProg.operation (.llvm .mlir__constant) #[] #[dstTy] props)
    (fun result => result.res[0]!)

private theorem zext_i1_nneg_refines_zero {w : Nat} (h : 1 < w) (x : LLVM.Int 1) :
    LLVM.Int.zext x w true h ⊒ .val (BitVec.ofInt w 0) := by
  cases x with
  | poison => simp [LLVM.Int.zext, Id.run]
  | val x =>
    rcases BitVec.eq_zero_or_eq_one x with rfl | rfl
    · simp [LLVM.Int.zext, Id.run, isRefinedBy_eq]
    · change LLVM.Int.poison ⊒ (.val (BitVec.ofInt w 0))
      exact poison_isRefinedBy _

public theorem zextNNegI1ToZero_valid : Pattern.Valid zextNNegI1ToZero := by
  simp only [zextNNegI1ToZero]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  rintro srcType ⟨srcW, srcSignedness⟩ hSrc hSrcW
  subst srcType
  change srcW = 1 at hSrcW
  subst srcW
  rintro ⟨dstW, dstSignedness⟩
  rintro x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int 1 at x
  rintro props source hFlag hSource
  have hFlag' : props.nneg = true := of_decide_eq_true hFlag
  obtain ⟨h1Dst, rfl⟩ := (zext_iff 1 dstW props x source).mp hSource
  rw [hFlag']
  simp [zeroProperty, IsTypeAttr.cast?_of]
  refine ⟨.int dstW (.val (BitVec.ofInt dstW 0)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg
      (fun z => RuntimeValue.int dstW (.val z))
      (ofInt_normalizeValue { bitwidth := dstW, signedness := dstSignedness } 0).symm
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using zext_i1_nneg_refines_zero h1Dst x

end Veir.Passes.InstCombineLLVM.ZExtNNegI1

#print axioms Veir.Passes.InstCombineLLVM.ZExtNNegI1.zextNNegI1ToZero_valid
