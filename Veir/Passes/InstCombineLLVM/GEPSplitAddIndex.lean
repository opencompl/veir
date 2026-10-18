module

public import Veir.Passes.InstCombineLLVM.GEPSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.GEPSplitAddIndex

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.GEPSemantics
open Veir.Passes.InstCombineLLVM.ProofTactics

private def splitAddIndex (gepProperties : GetelementptrProperties) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
      let idxTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let ptr ← MatchProg.value ptrTy
      let x ← MatchProg.value idxTy
      let y ← MatchProg.value idxTy
      let sum ← MatchProg.operation (.llvm .add) #[x, y] #[idxTy]
        (fun props => props == (default : propertiesOf (OpCode.llvm .add)))
      let _ ← MatchProg.root (.llvm .getelementptr) #[ptr, sum.res[0]!] #[ptrTy]
        (fun props => props == gepProperties)
      return (ptrTy, ptr, x, y))
    (fun (ptrTy, ptr, x, y) => do
      let gepProps ← CreateProg.property (.llvm .getelementptr) gepProperties
      let first ← CreateProg.operation (.llvm .getelementptr) #[ptr, x] #[ptrTy]
        gepProps
      CreateProg.operation (.llvm .getelementptr) #[first.res[0]!, y] #[ptrTy]
        gepProps)
    (fun result => result.res[0]!)

/-- InstructionCombining.cpp:3657-3685, specialized to an unflagged RV64
    one-index `i32` GEP whose i64 index is an unflagged add. -/
public def gepSplitAddIndex : Pattern OpCode := splitAddIndex dynamicGepI32Properties

private theorem splitAddIndex_valid (gepProperties : GetelementptrProperties)
    (stride : Nat)
    (hSemantics : ∀ (ptrTy : LLVM.PointerType) (ptr : LLVM.Ptr)
      (idx : LLVM.Int 64) (result : RuntimeValue),
      InterpretsTo (.llvm .getelementptr) gepProperties #[ptrTy]
        #[.addr ptr, .int 64 idx] #[result] ↔
        result = .addr (gepResult stride ptr idx)) :
    Pattern.Valid (splitAddIndex gepProperties) := by
  simp only [splitAddIndex]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpPuddleSemantics
  rintro ptrTy _ ⟨idxW, idxSignedness⟩ rfl hWidth ptr hPtr x hX y hY
  change idxW = 64 at hWidth
  subst idxW
  obtain ⟨ptr, rfl⟩ := RuntimeValue.Conforms.llvmPointerType.mp hPtr
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType.mp hY
  rintro addProps sum hAddProps hAdd
  subst addProps
  obtain rfl := (add_iff 64 default x y sum).mp hAdd
  rintro gepProps source hGepProps hSource
  have hGepPropsEq : gepProps = gepProperties := beq_iff_eq.mp hGepProps
  subst gepProps
  obtain rfl := (hSemantics ptrTy ptr (LLVM.Int.add x y false false) source).mp hSource
  refine ⟨.addr (gepResult stride ptr x),
    (hSemantics ptrTy ptr x _).mpr rfl, ?_⟩
  refine ⟨.addr (gepResult stride (gepResult stride ptr x) y),
    (hSemantics ptrTy (gepResult stride ptr x) y _).mpr rfl, ?_⟩
  rw [gepResult_add_i64]
  simp

public theorem gepSplitAddIndex_valid : Pattern.Valid gepSplitAddIndex := by
  apply splitAddIndex_valid dynamicGepI32Properties 4
  intro ptrTy ptr idx result
  exact gep_i32_iff ptrTy ptr idx result

end Veir.Passes.InstCombineLLVM.GEPSplitAddIndex

#print axioms Veir.Passes.InstCombineLLVM.GEPSplitAddIndex.gepSplitAddIndex_valid
