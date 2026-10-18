module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NotAndXorOr

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

/-- Canonical shared-first-operand scalar specialization of
    InstCombineAndOrXor.cpp:5064-5067. -/
private def notAndXorOrPattern (andCommuted orCommuted notConstantLeft : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let d ← MatchProg.value ty
    let minusOne ← matchIntConstantNormalized ty (-1)
    let both ← if andCommuted then
      MatchProg.operation (.llvm .and) #[b, a] #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
    let either ← if orCommuted then
      MatchProg.operation (.llvm .or) #[d, a] #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .or) #[a, d] #[ty] (fun _ => true)
    let xor ← MatchProg.operation (.llvm .xor) #[both.res[0]!, either.res[0]!]
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
private theorem notAndXorOrPattern_valid (andCommuted orCommuted notConstantLeft : Bool) :
    Pattern.Valid (notAndXorOrPattern andCommuted orCommuted notConstantLeft) := by
  cases andCommuted <;> cases orCommuted <;> cases notConstantLeft <;>
    simp only [notAndXorOrPattern, matchIntConstantNormalized, Bool.false_eq_true,
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
      rintro ⟨⟩ both hBoth
      obtain rfl := (and_iff _ _ _ _).mp hBoth
      rintro orProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
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
        | rw [LLVM.Int.cast_self, not_shared_and_xor_or]
        | rw [LLVM.Int.cast_self, llvm_xor_comm, not_shared_and_xor_or]
        exact isRefinedBy_refl _
      | refine ⟨.int w (LLVM.Int.xor (LLVM.Int.or d a orProps.disjoint)
            (.val (BitVec.ofInt w (-1)))), (xor_iff _ _ _ _).mpr rfl, ?_⟩
        refine ⟨.int w (LLVM.Int.or (LLVM.Int.and a b)
            (LLVM.Int.xor (LLVM.Int.or d a orProps.disjoint)
              (.val (BitVec.ofInt w (-1))))), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
        refine ⟨rfl, ?_⟩
        first
        | rw [LLVM.Int.cast_self, not_shared_and_xor_commuted_or]
        | rw [LLVM.Int.cast_self, llvm_xor_comm, not_shared_and_xor_commuted_or]
        exact isRefinedBy_refl _
      | refine ⟨.int w (LLVM.Int.xor (LLVM.Int.or a d orProps.disjoint)
            (.val (BitVec.ofInt w (-1)))), (xor_iff _ _ _ _).mpr rfl, ?_⟩
        refine ⟨.int w (LLVM.Int.or (LLVM.Int.and b a)
            (LLVM.Int.xor (LLVM.Int.or a d orProps.disjoint)
              (.val (BitVec.ofInt w (-1))))), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
        refine ⟨rfl, ?_⟩
        first
        | rw [LLVM.Int.cast_self, not_commuted_and_xor_or]
        | rw [LLVM.Int.cast_self, llvm_xor_comm, not_commuted_and_xor_or]
        exact isRefinedBy_refl _
      | refine ⟨.int w (LLVM.Int.xor (LLVM.Int.or d a orProps.disjoint)
            (.val (BitVec.ofInt w (-1)))), (xor_iff _ _ _ _).mpr rfl, ?_⟩
        refine ⟨.int w (LLVM.Int.or (LLVM.Int.and b a)
            (LLVM.Int.xor (LLVM.Int.or d a orProps.disjoint)
              (.val (BitVec.ofInt w (-1))))), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
        refine ⟨rfl, ?_⟩
        first
        | rw [LLVM.Int.cast_self, not_commuted_and_xor_commuted_or]
        | rw [LLVM.Int.cast_self, llvm_xor_comm, not_commuted_and_xor_commuted_or]
        exact isRefinedBy_refl _

public def notAndXorOr : Pattern OpCode := notAndXorOrPattern false false false
public theorem notAndXorOr_valid : Pattern.Valid notAndXorOr :=
  notAndXorOrPattern_valid false false false

public def notAndXorCommutedOr : Pattern OpCode := notAndXorOrPattern false true false
public theorem notAndXorCommutedOr_valid : Pattern.Valid notAndXorCommutedOr :=
  notAndXorOrPattern_valid false true false

public def notCommutedAndXorOr : Pattern OpCode := notAndXorOrPattern true false false
public theorem notCommutedAndXorOr_valid : Pattern.Valid notCommutedAndXorOr :=
  notAndXorOrPattern_valid true false false

public def notCommutedAndXorCommutedOr : Pattern OpCode :=
  notAndXorOrPattern true true false
public theorem notCommutedAndXorCommutedOr_valid :
    Pattern.Valid notCommutedAndXorCommutedOr :=
  notAndXorOrPattern_valid true true false


public def notAndXorOrConstantLeft : Pattern OpCode := notAndXorOrPattern false false true
public theorem notAndXorOrConstantLeft_valid : Pattern.Valid notAndXorOrConstantLeft :=
  notAndXorOrPattern_valid false false true

public def notAndXorCommutedOrConstantLeft : Pattern OpCode := notAndXorOrPattern false true true
public theorem notAndXorCommutedOrConstantLeft_valid : Pattern.Valid notAndXorCommutedOrConstantLeft :=
  notAndXorOrPattern_valid false true true

public def notCommutedAndXorOrConstantLeft : Pattern OpCode := notAndXorOrPattern true false true
public theorem notCommutedAndXorOrConstantLeft_valid : Pattern.Valid notCommutedAndXorOrConstantLeft :=
  notAndXorOrPattern_valid true false true

public def notCommutedAndXorCommutedOrConstantLeft : Pattern OpCode := notAndXorOrPattern true true true
public theorem notCommutedAndXorCommutedOrConstantLeft_valid : Pattern.Valid notCommutedAndXorCommutedOrConstantLeft :=
  notAndXorOrPattern_valid true true true

end Veir.Passes.InstCombineLLVM.NotAndXorOr
