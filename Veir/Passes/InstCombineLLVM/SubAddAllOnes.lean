module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SubAddAllOnes

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineAddSub.cpp:2535-2538:
    `(X + -1) - Y -> ~Y + X`. -/
public def subAddAllOnes : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let minusOne ← matchIntConstantNormalized ty (-1)
    let dec ← MatchProg.operation (.llvm .add) #[x, minusOne] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[dec.res[0]!, y] #[ty] (fun _ => true)
    return (ty, x, y, minusOne))
  (fun (ty, x, y, minusOne) => do
    let xp ← CreateProg.property (.llvm .xor) ()
    let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne] #[ty] xp
    let ap ← CreateProg.property (.llvm .add) default
    CreateProg.operation (.llvm .add) #[notY.res[0]!, x] #[ty] ap)
  (fun result => result.res[0]!)

public theorem subAddAllOnes_valid : Pattern.Valid subAddAllOnes := by
  simp only [subAddAllOnes, matchIntConstantNormalized]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpScalarPuddleSemantics
  rintro ⟨w, signedness⟩ x y
  rintro ⟨constantValue⟩ minusOne hInterpMinusOne
  cases constantValue with
  | float _ | dense _ | string _ =>
    rintro _ _ _ _ _ _ hMinusOne
    simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
  | integer minusOneAttr =>
    obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
    rintro addProps dec hDec
    obtain rfl := (add_iff _ _ _ _ _).mp hDec
    rintro subProps source hSource
    obtain rfl := (sub_iff _ _ _ _ _).mp hSource
    rintro hMinusOne
    have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
      simpa [isNormalizedIntConstant, asLLVMConstantProperties,
        IsTypeAttr.cast?_of] using hMinusOne
    rw [hMinusOneBits]
    refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
      (xor_iff _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int w (LLVM.Int.add
        (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))) x),
      (add_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (sub_add_allones_refines_not_add w x y addProps.nsw addProps.nuw
        subProps.nsw subProps.nuw)

end Veir.Passes.InstCombineLLVM.SubAddAllOnes
