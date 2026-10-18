module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NotOrXorAnd

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

/-- Canonical shared-first-operand scalar specialization of the commuted branch
    at InstCombineAndOrXor.cpp:5072-5075. -/
private def notOrXorAndPattern (andCommuted orCommuted notConstantLeft : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let d ← MatchProg.value ty
    let minusOne ← matchIntConstantNormalized ty (-1)
    let either ← if orCommuted then
      MatchProg.operation (.llvm .or) #[d, a] #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .or) #[a, d] #[ty] (fun _ => true)
    let both ← if andCommuted then
      MatchProg.operation (.llvm .and) #[b, a] #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
    let xor ← MatchProg.operation (.llvm .xor) #[either.res[0]!, both.res[0]!]
      #[ty] (fun _ => true)
    let _ ← if notConstantLeft then
      MatchProg.root (.llvm .xor) #[minusOne, xor.res[0]!] #[ty] (fun _ => true)
    else
      MatchProg.root (.llvm .xor) #[xor.res[0]!, minusOne] #[ty] (fun _ => true)
    return (ty, both.res[0]!, either.res[0]!, minusOne))
  (fun (ty, both, either, minusOne) => do
    let xp ← CreateProg.property (.llvm .xor) ()
    let notEither ← CreateProg.operation (.llvm .xor) #[either, minusOne] #[ty] xp
    let op ← CreateProg.property (.llvm .or) default
    CreateProg.operation (.llvm .or) #[both, notEither.res[0]!] #[ty] op)
  (fun result => result.res[0]!)

set_option maxHeartbeats 800000 in
private theorem notOrXorAndPattern_valid (andCommuted orCommuted notConstantLeft : Bool) :
    Pattern.Valid (notOrXorAndPattern andCommuted orCommuted notConstantLeft) := by
  cases andCommuted <;> cases orCommuted <;> cases notConstantLeft <;>
    simp only [notOrXorAndPattern, matchIntConstantNormalized, Bool.false_eq_true,
      ite_false, ite_true]
  all_goals
    unfoldPuddleBuilder
    proveScalarPuddleStructure
    simpScalarPuddleSemantics
    rintro ⟨w, signedness⟩ a b d
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro orProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
      rintro ⟨⟩ both hBoth
      obtain rfl := (and_iff _ _ _ _).mp hBoth
      rintro ⟨⟩ xor hXor
      obtain rfl := (xor_iff _ _ _ _).mp hXor
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      first
      | refine ⟨.int w (LLVM.Int.xor (LLVM.Int.or a d orProps.disjoint)
            (.val (BitVec.ofInt w (-1)))), (xor_iff _ _ _ _).mpr rfl, ?_⟩
        refine ⟨.int w (LLVM.Int.or (LLVM.Int.and a b)
            (LLVM.Int.xor (LLVM.Int.or a d orProps.disjoint)
              (.val (BitVec.ofInt w (-1))))), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
        refine ⟨rfl, ?_⟩
        first
        | rw [LLVM.Int.cast_self, not_shared_or_xor_and]
        | rw [LLVM.Int.cast_self, llvm_xor_comm, not_shared_or_xor_and]
        exact isRefinedBy_refl _
      | refine ⟨.int w (LLVM.Int.xor (LLVM.Int.or d a orProps.disjoint)
            (.val (BitVec.ofInt w (-1)))), (xor_iff _ _ _ _).mpr rfl, ?_⟩
        refine ⟨.int w (LLVM.Int.or (LLVM.Int.and a b)
            (LLVM.Int.xor (LLVM.Int.or d a orProps.disjoint)
              (.val (BitVec.ofInt w (-1))))), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
        refine ⟨rfl, ?_⟩
        first
        | rw [LLVM.Int.cast_self, not_commuted_or_xor_and]
        | rw [LLVM.Int.cast_self, llvm_xor_comm, not_commuted_or_xor_and]
        exact isRefinedBy_refl _
      | refine ⟨.int w (LLVM.Int.xor (LLVM.Int.or a d orProps.disjoint)
            (.val (BitVec.ofInt w (-1)))), (xor_iff _ _ _ _).mpr rfl, ?_⟩
        refine ⟨.int w (LLVM.Int.or (LLVM.Int.and b a)
            (LLVM.Int.xor (LLVM.Int.or a d orProps.disjoint)
              (.val (BitVec.ofInt w (-1))))), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
        refine ⟨rfl, ?_⟩
        first
        | rw [LLVM.Int.cast_self, not_or_xor_commuted_and]
        | rw [LLVM.Int.cast_self, llvm_xor_comm, not_or_xor_commuted_and]
        exact isRefinedBy_refl _
      | refine ⟨.int w (LLVM.Int.xor (LLVM.Int.or d a orProps.disjoint)
            (.val (BitVec.ofInt w (-1)))), (xor_iff _ _ _ _).mpr rfl, ?_⟩
        refine ⟨.int w (LLVM.Int.or (LLVM.Int.and b a)
            (LLVM.Int.xor (LLVM.Int.or d a orProps.disjoint)
              (.val (BitVec.ofInt w (-1))))), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
        refine ⟨rfl, ?_⟩
        first
        | rw [LLVM.Int.cast_self, not_commuted_or_xor_commuted_and]
        | rw [LLVM.Int.cast_self, llvm_xor_comm, not_commuted_or_xor_commuted_and]
        exact isRefinedBy_refl _

public def notOrXorAnd : Pattern OpCode := notOrXorAndPattern false false false
public theorem notOrXorAnd_valid : Pattern.Valid notOrXorAnd :=
  notOrXorAndPattern_valid false false false

public def notCommutedOrXorAnd : Pattern OpCode := notOrXorAndPattern false true false
public theorem notCommutedOrXorAnd_valid : Pattern.Valid notCommutedOrXorAnd :=
  notOrXorAndPattern_valid false true false

public def notOrXorCommutedAnd : Pattern OpCode := notOrXorAndPattern true false false
public theorem notOrXorCommutedAnd_valid : Pattern.Valid notOrXorCommutedAnd :=
  notOrXorAndPattern_valid true false false

public def notCommutedOrXorCommutedAnd : Pattern OpCode :=
  notOrXorAndPattern true true false
public theorem notCommutedOrXorCommutedAnd_valid :
    Pattern.Valid notCommutedOrXorCommutedAnd :=
  notOrXorAndPattern_valid true true false


public def notOrXorAndConstantLeft : Pattern OpCode := notOrXorAndPattern false false true
public theorem notOrXorAndConstantLeft_valid : Pattern.Valid notOrXorAndConstantLeft :=
  notOrXorAndPattern_valid false false true

public def notCommutedOrXorAndConstantLeft : Pattern OpCode := notOrXorAndPattern false true true
public theorem notCommutedOrXorAndConstantLeft_valid : Pattern.Valid notCommutedOrXorAndConstantLeft :=
  notOrXorAndPattern_valid false true true

public def notOrXorCommutedAndConstantLeft : Pattern OpCode := notOrXorAndPattern true false true
public theorem notOrXorCommutedAndConstantLeft_valid : Pattern.Valid notOrXorCommutedAndConstantLeft :=
  notOrXorAndPattern_valid true false true

public def notCommutedOrXorCommutedAndConstantLeft : Pattern OpCode := notOrXorAndPattern true true true
public theorem notCommutedOrXorCommutedAndConstantLeft_valid : Pattern.Valid notCommutedOrXorCommutedAndConstantLeft :=
  notOrXorAndPattern_valid true true true

end Veir.Passes.InstCombineLLVM.NotOrXorAnd
