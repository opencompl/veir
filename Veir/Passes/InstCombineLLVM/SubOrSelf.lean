module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SubOrSelf

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

private def allOnesProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt (-1) intType))

private def subOrSelfPattern (commuted : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let either ← if commuted then
      MatchProg.operation (.llvm .or) #[y, x] #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .or) #[x, y] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[either.res[0]!, x] #[ty] (fun _ => true)
    return (ty, x, y))
  (fun (ty, x, y) => do
    let cp ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty allOnesProperty
    let minusOne ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] cp
    let xp ← CreateProg.property (.llvm .xor) ()
    let notX ← CreateProg.operation (.llvm .xor) #[x, minusOne.res[0]!] #[ty] xp
    let ap ← CreateProg.property (.llvm .and) ()
    CreateProg.operation (.llvm .and) #[notX.res[0]!, y] #[ty] ap)
  (fun result => result.res[0]!)

private theorem subOrSelfPattern_valid (commuted : Bool) :
    Pattern.Valid (subOrSelfPattern commuted) := by
  cases commuted <;> simp only [subOrSelfPattern, Bool.false_eq_true, ite_false, ite_true] <;>
    unfoldPuddleBuilder
  all_goals
    proveScalarPuddleStructure
    simpScalarPropertyPuddleSemantics
    rintro ⟨w, signedness⟩ x y
    rintro orProps either hEither
    obtain rfl := (or_iff _ _ _ _ _).mp hEither
    rintro subProps source hSource
    obtain rfl := (sub_iff _ _ _ _ _).mp hSource
    simp [allOnesProperty, IsTypeAttr.cast?_of]
    refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg
        (fun z => RuntimeValue.int w (.val z))
        (ofInt_normalizeValue { bitwidth := w, signedness := signedness } (-1)).symm
    refine ⟨.int w (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))), ?_, ?_⟩
    · exact (xor_iff _ _ _ _).mpr rfl
    refine ⟨.int w (LLVM.Int.and
      (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y), ?_, ?_⟩
    · exact (and_iff _ _ _ _).mpr rfl
    refine ⟨rfl, ?_⟩
    first
    | simpa only [LLVM.Int.cast_self] using
        (sub_or_self_refines_and_not w x y orProps.disjoint subProps.nsw subProps.nuw)
    | simpa only [LLVM.Int.cast_self, llvm_or_comm] using
        (sub_or_self_refines_and_not w x y orProps.disjoint subProps.nsw subProps.nuw)

/-- InstCombineAddSub.cpp:2779-2784, canonical OR operand order. -/
public def subOrSelf : Pattern OpCode := subOrSelfPattern false
public theorem subOrSelf_valid : Pattern.Valid subOrSelf := subOrSelfPattern_valid false

/-- Source-supported commuted OR operand order. -/
public def subCommutedOrSelf : Pattern OpCode := subOrSelfPattern true
public theorem subCommutedOrSelf_valid : Pattern.Valid subCommutedOrSelf :=
  subOrSelfPattern_valid true

end Veir.Passes.InstCombineLLVM.SubOrSelf
