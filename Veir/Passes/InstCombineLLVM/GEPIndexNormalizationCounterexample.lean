module

public import Veir.PatternRewriter.Puddle.Validity
public import Veir.Data.LLVM.Int.Lemmas
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.GEPIndexNormalizationCounterexample

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

private theorem integerType_of_val (t : IntegerType) :
    (TypeAttr.of IntegerType t).val = .integerType t := by
  rw [TypeAttr.of_val]
  exact (Attribute.integerType_eq_of t).symm

private theorem sext_iff {signedness : IntegerType.Signedness} (w₁ w₂ : Nat)
    (x : LLVM.Int w₁) (v : RuntimeValue) :
    InterpretsTo (.llvm .sext) () #[IntegerType.mk w₂ signedness]
      #[.int w₁ x] #[v] ↔
      ∃ h : w₁ < w₂, v = .int w₂ (LLVM.Int.sext x w₂ h) := by
  have hResultType :
      (#[TypeAttr.of IntegerType (IntegerType.mk w₂ signedness)][0]? : Option TypeAttr) =
        some (TypeAttr.of IntegerType (IntegerType.mk w₂ signedness)) := by
    rfl
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val] at hv
    split at hv
    · contradiction
    · exact ⟨by omega, by simpa using hv.symm⟩
  · rintro ⟨hw, rfl⟩
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val]
      have hn : ¬w₂ ≤ w₁ := by omega
      simp [hn]

private def dynamicI8GepProperties : GetelementptrProperties :=
  { rawConstantIndices :=
      { elementType := IntegerType.signless 32, values := #[(-2147483648 : Int)] }
    elem_type := ({ bitwidth := 8, signedness := .signless } : IntegerType)
    noWrapFlags := { value := 0, type := IntegerType.signless 32 } }

/-- The narrow scalar-index arm of `visitGetElementPtrInst`: on RV64, replace
    an unflagged dynamic `i8` GEP index by its `i64` sign extension. -/
public def normalizeNarrowGepIndex : Pattern OpCode := Pattern.Builder
  (do
    let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
    let idxTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 8)
    let ptr ← MatchProg.value ptrTy
    let idx ← MatchProg.value idxTy
    let root ← MatchProg.root (.llvm .getelementptr) #[ptr, idx] #[ptrTy]
      (fun props => props == dynamicI8GepProperties)
    return (ptrTy, ptr, idx, root.properties))
  (fun (ptrTy, ptr, idx, gepProps) => do
    let wideTy ← CreateProg.type
      ({ bitwidth := 64, signedness := .signless } : IntegerType)
    let sextProps ← CreateProg.property (.llvm .sext) ()
    let wideIdx ← CreateProg.operation (.llvm .sext) #[idx] #[wideTy] sextProps
    CreateProg.operation (.llvm .getelementptr) #[ptr, wideIdx.res[0]!]
      #[ptrTy] gepProps)
  (fun result => result.res[0]!)

private theorem normalizeNarrowGepIndex_not_preserves :
    ¬ normalizeNarrowGepIndex.PreservesSemantics := by
  simp only [normalizeNarrowGepIndex]
  unfoldPuddleBuilder
  simpPuddleSemantics
  let i8 : IntegerType := { bitwidth := 8, signedness := .signless }
  refine ⟨(default : LLVM.PointerType),
    (i8 : TypeAttr), i8, rfl, rfl,
    .addr (.val ⟨0, 0⟩), ?_,
    .int 8 (.val (BitVec.ofNat 8 255)), ?_,
    dynamicI8GepProperties, beq_iff_eq.mpr rfl,
    .addr (.val ⟨0, UInt64.ofNat 255⟩), ?_, ?_⟩
  · exact RuntimeValue.Conforms.llvmPointerType.mpr ⟨.val ⟨0, 0⟩, rfl⟩
  · exact RuntimeValue.Conforms.integerType.mpr ⟨.val (BitVec.ofNat 8 255), rfl⟩
  · have hSize : DataLayout.riscv64.getTypeAllocSize
        (Attribute.of IntegerType
          ({ bitwidth := 8, signedness := .signless } : IntegerType)) = some 1 := by
      rw [← Attribute.integerType_eq_of
        ({ bitwidth := 8, signedness := .signless } : IntegerType)]
      exact DataLayout.riscv64_getTypeAllocSize_i8
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', dynamicI8GepProperties,
        TypeAttr.of_val]
      rw [hSize]
      simp
  · intro wideIdx hSext target hTarget
    obtain ⟨h8_64, rfl⟩ := (sext_iff 8 64
      (.val (BitVec.ofNat 8 255)) wideIdx).mp hSext
    have hSize : DataLayout.riscv64.getTypeAllocSize
        (Attribute.of IntegerType
          ({ bitwidth := 8, signedness := .signless } : IntegerType)) = some 1 := by
      rw [← Attribute.integerType_eq_of
        ({ bitwidth := 8, signedness := .signless } : IntegerType)]
      exact DataLayout.riscv64_getTypeAllocSize_i8
    have hv := hTarget.2 MemoryState.empty
    simp only [interpretOp', Llvm.interpretOp', dynamicI8GepProperties,
      TypeAttr.of_val] at hv
    rw [hSize] at hv
    have hSignExtend : LLVM.Int.sext (.val (BitVec.ofNat 8 255)) 64 h8_64 =
        .val (BitVec.ofInt 64 (-1)) := by
      simp [LLVM.Int.sext, Id.run]
    rw [hSignExtend] at hv
    simp at hv
    subst target
    simp [RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy]

/-- Puddle interprets every GEP index with `BitVec.toNat`, while LLVM
    sign-extends a narrow index before address calculation. Thus index `255 :
    i8` denotes `+255` in the modeled source GEP and `-1` after the explicit
    `sext`, producing distinct pointers. -/
public theorem normalizeNarrowGepIndex_not_valid :
    ¬ Pattern.Valid normalizeNarrowGepIndex := by
  intro h
  exact normalizeNarrowGepIndex_not_preserves h.refines

end Veir.Passes.InstCombineLLVM.GEPIndexNormalizationCounterexample

#print axioms Veir.Passes.InstCombineLLVM.GEPIndexNormalizationCounterexample.normalizeNarrowGepIndex_not_valid
