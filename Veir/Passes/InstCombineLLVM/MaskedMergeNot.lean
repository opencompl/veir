module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.MaskedMergeNot

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

/-- Canonical scalar specialization of InstCombineAndOrXor.cpp:5028-5031:
    `B xor ((B xor X) & ~M) -> ((B xor X) & M) xor X`. -/
private def maskedMergeNotPattern
    (rootCommuted andCommuted deltaCommuted notConstantLeft : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let b ← MatchProg.value ty
    let x ← MatchProg.value ty
    let m ← MatchProg.value ty
    let minusOne ← matchIntConstantNormalized ty (-1)
    let delta ← if deltaCommuted then
      MatchProg.operation (.llvm .xor) #[x, b] #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .xor) #[b, x] #[ty] (fun _ => true)
    let notMask ← if notConstantLeft then
      MatchProg.operation (.llvm .xor) #[minusOne, m] #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .xor) #[m, minusOne] #[ty] (fun _ => true)
    let masked ← if andCommuted then
      MatchProg.operation (.llvm .and) #[notMask.res[0]!, delta.res[0]!]
        #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .and) #[delta.res[0]!, notMask.res[0]!]
        #[ty] (fun _ => true)
    let _ ← if rootCommuted then
      MatchProg.root (.llvm .xor) #[masked.res[0]!, b] #[ty] (fun _ => true)
    else
      MatchProg.root (.llvm .xor) #[b, masked.res[0]!] #[ty] (fun _ => true)
    return (ty, x, m, delta.res[0]!))
  (fun (ty, x, m, delta) => do
    let ap ← CreateProg.property (.llvm .and) ()
    let masked ← CreateProg.operation (.llvm .and) #[delta, m] #[ty] ap
    let xp ← CreateProg.property (.llvm .xor) ()
    CreateProg.operation (.llvm .xor) #[masked.res[0]!, x] #[ty] xp)
  (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem maskedMergeNotPattern_valid
    (rootCommuted andCommuted deltaCommuted notConstantLeft : Bool) :
    Pattern.Valid (maskedMergeNotPattern rootCommuted andCommuted deltaCommuted notConstantLeft) := by
  cases rootCommuted <;> cases andCommuted <;> cases deltaCommuted <;>
    cases notConstantLeft <;>
    simp only [maskedMergeNotPattern, matchIntConstantNormalized, Bool.false_eq_true,
      ite_false, ite_true]
  all_goals
    unfoldPuddleBuilder
    proveScalarPuddleStructure
    simpScalarPuddleSemantics
    rintro ⟨w, signedness⟩ b x m
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ delta hDelta
      obtain rfl := (xor_iff _ _ _ _).mp hDelta
      rintro ⟨⟩ notMask hNotMask
      obtain rfl := (xor_iff _ _ _ _).mp hNotMask
      rintro ⟨⟩ masked hMasked
      obtain rfl := (and_iff _ _ _ _).mp hMasked
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w _, (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w _, (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      first
      | rw [LLVM.Int.cast_self, masked_merge_not_000]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, masked_merge_not_001]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, masked_merge_not_010]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, masked_merge_not_011]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, masked_merge_not_100]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, masked_merge_not_101]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, masked_merge_not_110]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, masked_merge_not_111]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, llvm_xor_comm (.val (BitVec.ofInt w (-1))) m,
          masked_merge_not_000]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, llvm_xor_comm (.val (BitVec.ofInt w (-1))) m,
          masked_merge_not_001]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, llvm_xor_comm (.val (BitVec.ofInt w (-1))) m,
          masked_merge_not_010]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, llvm_xor_comm (.val (BitVec.ofInt w (-1))) m,
          masked_merge_not_011]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, llvm_xor_comm (.val (BitVec.ofInt w (-1))) m,
          masked_merge_not_100]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, llvm_xor_comm (.val (BitVec.ofInt w (-1))) m,
          masked_merge_not_101]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, llvm_xor_comm (.val (BitVec.ofInt w (-1))) m,
          masked_merge_not_110]
        exact isRefinedBy_refl _
      | rw [LLVM.Int.cast_self, llvm_xor_comm (.val (BitVec.ofInt w (-1))) m,
          masked_merge_not_111]
        exact isRefinedBy_refl _

public def maskedMergeNot : Pattern OpCode := maskedMergeNotPattern false false false false
public theorem maskedMergeNot_valid : Pattern.Valid maskedMergeNot :=
  maskedMergeNotPattern_valid false false false false

public def maskedMergeNotDeltaCommuted : Pattern OpCode :=
  maskedMergeNotPattern false false true false
public theorem maskedMergeNotDeltaCommuted_valid : Pattern.Valid maskedMergeNotDeltaCommuted :=
  maskedMergeNotPattern_valid false false true false

public def maskedMergeNotAndCommuted : Pattern OpCode :=
  maskedMergeNotPattern false true false false
public theorem maskedMergeNotAndCommuted_valid : Pattern.Valid maskedMergeNotAndCommuted :=
  maskedMergeNotPattern_valid false true false false

public def maskedMergeNotAndDeltaCommuted : Pattern OpCode :=
  maskedMergeNotPattern false true true false
public theorem maskedMergeNotAndDeltaCommuted_valid :
    Pattern.Valid maskedMergeNotAndDeltaCommuted :=
  maskedMergeNotPattern_valid false true true false

public def maskedMergeNotRootCommuted : Pattern OpCode :=
  maskedMergeNotPattern true false false false
public theorem maskedMergeNotRootCommuted_valid : Pattern.Valid maskedMergeNotRootCommuted :=
  maskedMergeNotPattern_valid true false false false

public def maskedMergeNotRootDeltaCommuted : Pattern OpCode :=
  maskedMergeNotPattern true false true false
public theorem maskedMergeNotRootDeltaCommuted_valid :
    Pattern.Valid maskedMergeNotRootDeltaCommuted :=
  maskedMergeNotPattern_valid true false true false

public def maskedMergeNotRootAndCommuted : Pattern OpCode :=
  maskedMergeNotPattern true true false false
public theorem maskedMergeNotRootAndCommuted_valid :
    Pattern.Valid maskedMergeNotRootAndCommuted :=
  maskedMergeNotPattern_valid true true false false

public def maskedMergeNotAllCommuted : Pattern OpCode :=
  maskedMergeNotPattern true true true false
public theorem maskedMergeNotAllCommuted_valid : Pattern.Valid maskedMergeNotAllCommuted :=
  maskedMergeNotPattern_valid true true true false


/-- Variants where LLVM's `m_Not` matches the constant-left spelling `xor -1, M`. -/
public def maskedMergeNotNotLeft : Pattern OpCode :=
  maskedMergeNotPattern false false false true
public theorem maskedMergeNotNotLeft_valid : Pattern.Valid maskedMergeNotNotLeft :=
  maskedMergeNotPattern_valid false false false true

public def maskedMergeNotDeltaCommutedNotLeft : Pattern OpCode :=
  maskedMergeNotPattern false false true true
public theorem maskedMergeNotDeltaCommutedNotLeft_valid :
    Pattern.Valid maskedMergeNotDeltaCommutedNotLeft :=
  maskedMergeNotPattern_valid false false true true

public def maskedMergeNotAndCommutedNotLeft : Pattern OpCode :=
  maskedMergeNotPattern false true false true
public theorem maskedMergeNotAndCommutedNotLeft_valid :
    Pattern.Valid maskedMergeNotAndCommutedNotLeft :=
  maskedMergeNotPattern_valid false true false true

public def maskedMergeNotAndDeltaCommutedNotLeft : Pattern OpCode :=
  maskedMergeNotPattern false true true true
public theorem maskedMergeNotAndDeltaCommutedNotLeft_valid :
    Pattern.Valid maskedMergeNotAndDeltaCommutedNotLeft :=
  maskedMergeNotPattern_valid false true true true

public def maskedMergeNotRootCommutedNotLeft : Pattern OpCode :=
  maskedMergeNotPattern true false false true
public theorem maskedMergeNotRootCommutedNotLeft_valid :
    Pattern.Valid maskedMergeNotRootCommutedNotLeft :=
  maskedMergeNotPattern_valid true false false true

public def maskedMergeNotRootDeltaCommutedNotLeft : Pattern OpCode :=
  maskedMergeNotPattern true false true true
public theorem maskedMergeNotRootDeltaCommutedNotLeft_valid :
    Pattern.Valid maskedMergeNotRootDeltaCommutedNotLeft :=
  maskedMergeNotPattern_valid true false true true

public def maskedMergeNotRootAndCommutedNotLeft : Pattern OpCode :=
  maskedMergeNotPattern true true false true
public theorem maskedMergeNotRootAndCommutedNotLeft_valid :
    Pattern.Valid maskedMergeNotRootAndCommutedNotLeft :=
  maskedMergeNotPattern_valid true true false true

public def maskedMergeNotAllCommutedNotLeft : Pattern OpCode :=
  maskedMergeNotPattern true true true true
public theorem maskedMergeNotAllCommutedNotLeft_valid :
    Pattern.Valid maskedMergeNotAllCommutedNotLeft :=
  maskedMergeNotPattern_valid true true true true

end Veir.Passes.InstCombineLLVM.MaskedMergeNot
