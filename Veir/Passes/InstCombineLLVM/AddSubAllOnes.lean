module

public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.AddSubAllOnes

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineAddSub.cpp:882-886:
    `add (sub X, Y), -1 -> add (not Y), X`. The source one-use check is a
    profitability guard; the scalar identity remains valid without it. -/
public def addSubAllOnes : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let sub ← MatchProg.operation (.llvm .sub) #[x, y] #[ty] (fun _ => true)
    let minusOne ← matchIntConstantNormalized ty (-1)
    let _ ← MatchProg.root (.llvm .add) #[sub.res[0]!, minusOne] #[ty] (fun _ => true)
    return (ty, x, y, minusOne))
  (fun (ty, x, y, minusOne) => do
    let xp ← CreateProg.property (.llvm .xor) ()
    let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne] #[ty] xp
    let ap ← CreateProg.property (.llvm .add) default
    CreateProg.operation (.llvm .add) #[notY.res[0]!, x] #[ty] ap)
  (fun result => result.res[0]!)

set_option linter.tacticCheckInstances false in
public theorem addSubAllOnes_valid : Pattern.Valid addSubAllOnes := by
  simp only [addSubAllOnes, matchIntConstantNormalized]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpScalarPuddleSemantics
  rintro ⟨w, signedness⟩ x y
  rintro subProps sub hSub
  obtain rfl := (sub_iff _ _ _ _ _).mp hSub
  rintro ⟨constantValue⟩ minusOne hInterpMinusOne
  cases constantValue with
  | float _ | dense _ | string _ =>
    rintro _ _ _ hMinusOne
    simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
  | integer minusOneAttr =>
    obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
    rintro addProps source hSource
    obtain rfl := (add_iff _ _ _ _ _).mp hSource
    rintro hMinusOne
    have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
      simpa [isNormalizedIntConstant, asLLVMConstantProperties,
        IsTypeAttr.cast?_of] using hMinusOne
    rw [hMinusOneBits]
    refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
      (xor_iff _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int w
        (LLVM.Int.add (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))) x),
      (add_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (add_sub_allones_refines_not_add w x y subProps.nsw subProps.nuw
        addProps.nsw addProps.nuw)

end Veir.Passes.InstCombineLLVM.AddSubAllOnes
