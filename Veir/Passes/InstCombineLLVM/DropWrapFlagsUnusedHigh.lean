module

public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.DropWrapFlagsUnusedHigh

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

private def dropWrapFlagsPattern (opcode : Llvm)
    (hasWrapFlag : propertiesOf (OpCode.llvm opcode) → Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm opcode) #[x, y] #[ty] hasWrapFlag
    return (ty, x, y))
  (fun (ty, x, y) => do
    let props ← CreateProg.property (.llvm opcode) default
    CreateProg.operation (.llvm opcode) #[x, y] #[ty] props)
  (fun result => result.res[0]!)

/-- Scalar `add` flag-clearing specialization of
    InstCombineSimplifyDemanded.cpp:240-252. -/
public def dropAddWrapFlags : Pattern OpCode :=
  dropWrapFlagsPattern .add (fun props => props.nsw || props.nuw)

/-- Scalar `sub` flag-clearing specialization of
    InstCombineSimplifyDemanded.cpp:240-252. -/
public def dropSubWrapFlags : Pattern OpCode :=
  dropWrapFlagsPattern .sub (fun props => props.nsw || props.nuw)

/-- Scalar `mul` flag-clearing specialization of
    InstCombineSimplifyDemanded.cpp:240-252. -/
public def dropMulWrapFlags : Pattern OpCode :=
  dropWrapFlagsPattern .mul (fun props => props.nsw || props.nuw)

public theorem dropAddWrapFlags_valid : Pattern.Valid dropAddWrapFlags := by
  simp only [dropAddWrapFlags, dropWrapFlagsPattern]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpScalarPuddleSemantics
  rintro ⟨w, signedness⟩ x y props result _hFlags hResult
  obtain rfl := (add_iff _ _ _ _ _).mp hResult
  refine ⟨.int w (LLVM.Int.add x y), (add_iff _ default _ _ _).mpr rfl, ?_⟩
  exact ⟨rfl, by simpa only [LLVM.Int.cast_self] using add_flags_refine w x y props.nsw props.nuw⟩

public theorem dropSubWrapFlags_valid : Pattern.Valid dropSubWrapFlags := by
  simp only [dropSubWrapFlags, dropWrapFlagsPattern]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpScalarPuddleSemantics
  rintro ⟨w, signedness⟩ x y props result _hFlags hResult
  obtain rfl := (sub_iff _ _ _ _ _).mp hResult
  refine ⟨.int w (LLVM.Int.sub x y), (sub_iff _ default _ _ _).mpr rfl, ?_⟩
  exact ⟨rfl, by simpa only [LLVM.Int.cast_self] using sub_flags_refine w x y props.nsw props.nuw⟩

public theorem dropMulWrapFlags_valid : Pattern.Valid dropMulWrapFlags := by
  simp only [dropMulWrapFlags, dropWrapFlagsPattern]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpScalarPuddleSemantics
  rintro ⟨w, signedness⟩ x y props result _hFlags hResult
  obtain rfl := (mul_iff _ _ _ _ _).mp hResult
  refine ⟨.int w (LLVM.Int.mul x y), (mul_iff _ default _ _ _).mpr rfl, ?_⟩
  exact ⟨rfl, by simpa only [LLVM.Int.cast_self] using mul_flags_refine w x y props.nsw props.nuw⟩

end Veir.Passes.InstCombineLLVM.DropWrapFlagsUnusedHigh
