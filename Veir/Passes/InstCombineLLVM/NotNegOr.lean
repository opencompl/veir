module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NotNegOr

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

/-- Scalar `~((-X) | Y) -> (X - 1) & ~Y` specialization of
    InstCombineAndOrXor.cpp:5298-5302. -/
public def notNegOr : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let minusOne ← matchIntConstantNormalized ty (-1)
    let neg ← MatchProg.operation (.llvm .sub) #[zero, x] #[ty] (fun _ => true)
    let either ← MatchProg.operation (.llvm .or) #[neg.res[0]!, y] #[ty]
      (fun _ => true)
    let _ ← MatchProg.root (.llvm .xor) #[either.res[0]!, minusOne] #[ty]
      (fun _ => true)
    return (ty, x, y, minusOne))
  (fun (ty, x, y, minusOne) => do
    let ap ← CreateProg.property (.llvm .add) default
    let dec ← CreateProg.operation (.llvm .add) #[x, minusOne] #[ty] ap
    let xp ← CreateProg.property (.llvm .xor) ()
    let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne] #[ty] xp
    let np ← CreateProg.property (.llvm .and) ()
    CreateProg.operation (.llvm .and) #[dec.res[0]!, notY.res[0]!] #[ty] np)
  (fun result => result.res[0]!)

/-- Commuted OR specialization from the same source matcher. -/
public def notOrNeg : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let minusOne ← matchIntConstantNormalized ty (-1)
    let neg ← MatchProg.operation (.llvm .sub) #[zero, x] #[ty] (fun _ => true)
    let either ← MatchProg.operation (.llvm .or) #[y, neg.res[0]!] #[ty]
      (fun _ => true)
    let _ ← MatchProg.root (.llvm .xor) #[either.res[0]!, minusOne] #[ty]
      (fun _ => true)
    return (ty, x, y, minusOne))
  (fun (ty, x, y, minusOne) => do
    let ap ← CreateProg.property (.llvm .add) default
    let dec ← CreateProg.operation (.llvm .add) #[x, minusOne] #[ty] ap
    let xp ← CreateProg.property (.llvm .xor) ()
    let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne] #[ty] xp
    let np ← CreateProg.property (.llvm .and) ()
    CreateProg.operation (.llvm .and) #[dec.res[0]!, notY.res[0]!] #[ty] np)
  (fun result => result.res[0]!)

public theorem notNegOr_valid : Pattern.Valid notNegOr := by
  simp only [notNegOr, matchIntConstant, matchIntConstantNormalized]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpScalarPuddleSemantics
  rintro ⟨w, signedness⟩ x y
  rintro ⟨zeroValue⟩ zero hZero hInterpZero
  cases zeroValue with
  | float _ | dense _ | string _ => simp at hZero
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro ⟨minusOneValue⟩ minusOne hInterpMinusOne
    cases minusOneValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro negProps neg hNeg
      obtain rfl := (sub_iff _ _ _ _ _).mp hNeg
      rintro orProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hZeroValue, hMinusOneBits]
      refine ⟨.int w (LLVM.Int.add x (.val (BitVec.ofInt w (-1)))),
        (add_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.and (LLVM.Int.add x (.val (BitVec.ofInt w (-1))))
          (LLVM.Int.xor y (.val (BitVec.ofInt w (-1))))),
        (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        (not_neg_or_refines_dec_and_not w x y negProps.nsw negProps.nuw
          orProps.disjoint)

public theorem notOrNeg_valid : Pattern.Valid notOrNeg := by
  simp only [notOrNeg, matchIntConstant, matchIntConstantNormalized]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpScalarPuddleSemantics
  rintro ⟨w, signedness⟩ x y
  rintro ⟨zeroValue⟩ zero hZero hInterpZero
  cases zeroValue with
  | float _ | dense _ | string _ => simp at hZero
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro ⟨minusOneValue⟩ minusOne hInterpMinusOne
    cases minusOneValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro negProps neg hNeg
      obtain rfl := (sub_iff _ _ _ _ _).mp hNeg
      rintro orProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hZeroValue, hMinusOneBits]
      refine ⟨.int w (LLVM.Int.add x (.val (BitVec.ofInt w (-1)))),
        (add_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.and (LLVM.Int.add x (.val (BitVec.ofInt w (-1))))
          (LLVM.Int.xor y (.val (BitVec.ofInt w (-1))))),
        (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        (not_or_neg_refines_dec_and_not w x y negProps.nsw negProps.nuw
          orProps.disjoint)


public def notNegOrConstantLeft : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let minusOne ← matchIntConstantNormalized ty (-1)
    let neg ← MatchProg.operation (.llvm .sub) #[zero, x] #[ty] (fun _ => true)
    let either ← MatchProg.operation (.llvm .or) #[neg.res[0]!, y] #[ty]
      (fun _ => true)
    let _ ← MatchProg.root (.llvm .xor) #[minusOne, either.res[0]!] #[ty]
      (fun _ => true)
    return (ty, x, y, minusOne))
  (fun (ty, x, y, minusOne) => do
    let ap ← CreateProg.property (.llvm .add) default
    let dec ← CreateProg.operation (.llvm .add) #[x, minusOne] #[ty] ap
    let xp ← CreateProg.property (.llvm .xor) ()
    let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne] #[ty] xp
    let np ← CreateProg.property (.llvm .and) ()
    CreateProg.operation (.llvm .and) #[dec.res[0]!, notY.res[0]!] #[ty] np)
  (fun result => result.res[0]!)

/-- Commuted OR specialization from the same source matcher. -/
public def notOrNegConstantLeft : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let minusOne ← matchIntConstantNormalized ty (-1)
    let neg ← MatchProg.operation (.llvm .sub) #[zero, x] #[ty] (fun _ => true)
    let either ← MatchProg.operation (.llvm .or) #[y, neg.res[0]!] #[ty]
      (fun _ => true)
    let _ ← MatchProg.root (.llvm .xor) #[minusOne, either.res[0]!] #[ty]
      (fun _ => true)
    return (ty, x, y, minusOne))
  (fun (ty, x, y, minusOne) => do
    let ap ← CreateProg.property (.llvm .add) default
    let dec ← CreateProg.operation (.llvm .add) #[x, minusOne] #[ty] ap
    let xp ← CreateProg.property (.llvm .xor) ()
    let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne] #[ty] xp
    let np ← CreateProg.property (.llvm .and) ()
    CreateProg.operation (.llvm .and) #[dec.res[0]!, notY.res[0]!] #[ty] np)
  (fun result => result.res[0]!)

public theorem notNegOrConstantLeft_valid : Pattern.Valid notNegOrConstantLeft := by
  simp only [notNegOrConstantLeft, matchIntConstant, matchIntConstantNormalized]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpScalarPuddleSemantics
  rintro ⟨w, signedness⟩ x y
  rintro ⟨zeroValue⟩ zero hZero hInterpZero
  cases zeroValue with
  | float _ | dense _ | string _ => simp at hZero
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro ⟨minusOneValue⟩ minusOne hInterpMinusOne
    cases minusOneValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro negProps neg hNeg
      obtain rfl := (sub_iff _ _ _ _ _).mp hNeg
      rintro orProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hZeroValue, hMinusOneBits]
      refine ⟨.int w (LLVM.Int.add x (.val (BitVec.ofInt w (-1)))),
        (add_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.and (LLVM.Int.add x (.val (BitVec.ofInt w (-1))))
          (LLVM.Int.xor y (.val (BitVec.ofInt w (-1))))),
        (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
        (not_neg_or_refines_dec_and_not w x y negProps.nsw negProps.nuw
          orProps.disjoint)

public theorem notOrNegConstantLeft_valid : Pattern.Valid notOrNegConstantLeft := by
  simp only [notOrNegConstantLeft, matchIntConstant, matchIntConstantNormalized]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpScalarPuddleSemantics
  rintro ⟨w, signedness⟩ x y
  rintro ⟨zeroValue⟩ zero hZero hInterpZero
  cases zeroValue with
  | float _ | dense _ | string _ => simp at hZero
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro ⟨minusOneValue⟩ minusOne hInterpMinusOne
    cases minusOneValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro negProps neg hNeg
      obtain rfl := (sub_iff _ _ _ _ _).mp hNeg
      rintro orProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hZeroValue, hMinusOneBits]
      refine ⟨.int w (LLVM.Int.add x (.val (BitVec.ofInt w (-1)))),
        (add_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.and (LLVM.Int.add x (.val (BitVec.ofInt w (-1))))
          (LLVM.Int.xor y (.val (BitVec.ofInt w (-1))))),
        (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
        (not_or_neg_refines_dec_and_not w x y negProps.nsw negProps.nuw
          orProps.disjoint)

end Veir.Passes.InstCombineLLVM.NotNegOr
